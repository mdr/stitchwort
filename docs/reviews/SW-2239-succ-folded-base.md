# SW-2239: review of merge `f90492dfe` (SW-2157, a folded call under `Succ`)

This is a review of SW-2157. That change alters what kernel conversion and
the unifier accept, so D2364 calls for an Opus review. I read code only: no
builds or runs.

What I read:

- The merge: `git show f90492dfe -m --first-parent`, and the lane's commit
  message (`b983cf323`).
- `crates/core/src/native.rs`: `view_with`, `from_view`, `nat_like`,
  `compare`, `compare_with`, `compare_lazily` and `view_to_call`.
- `crates/core/src/value.rs`: `conv_step` from the top to the numbers' rule,
  `is_folded`, `folded_call`, `folds`, `unfold_folded`, `needs_forcing`, and
  `Value::NatAdd`'s invariant.
- `crates/core/src/reference.rs`: `is_folded`, `unfold_folded`, `conv_in`
  down to the numbers' rule.
- `crates/elab/src/unify.rs`: `unify_step` from the forcing to the numbers'
  rule, `plus_rule`, `stuck_sum`, `plus_rule_with`'s start, `nested` and
  `run`'s start.
- `crates/core/src/budget.rs`: `step` (the stack floor).
- `crates/driver/tests/proofs/proof_equivalence.rs`: `terms`, `matrix`,
  `compared_alike`, `FIELDS_PROGRAM`, `FIELD_OPS` and the changed test.
- `examples/accept/succ-of-folded-call.sw`, the `docs/core.md` clause, and
  `docs/reviews/SW-2234-glued-call-against-number.md`.

## Summary

**The change is sound and does what it says.** At each of the four places,
`assign` now unfolds a folded base with `unfold_folded` and compares the
unfolding with the other side. That is a delta step through
`body_seen`, so hidden opaque bodies, pending group members and axioms
still never unfold. Everything newly accepted is definitional. The four
places take the same steps on the same inputs, so they agree, and the
matrix's transitivity check now holds on the depth-3 case SW-2234 found.
Removing SW-2211's rule loses nothing: `compare_lazily` forces the glued
call itself and reaches the same folded base, and I traced `wrap 0`
against `0` through to "equal" in every mode.

Neither of the lane's doubts is a real problem:

- `plus_rule` can't see a folded base in that position, so unfolding first
  takes nothing from it.
- The calls left inside the other side are compared lazily by `conv`,
  which is exactly as good as unfolding them first.

What's left is small. The unifier's new branch recurses on the Rust stack
once per level where `conv` iterates, and it can't postpone (F1). There are
test gaps (F3), and one invariant comment is now stretched (F2). No D
questions.

Top recommendations:

1. In `unify.rs`, push the unfolded pair onto `work` after `compare`
   returns, as `conv_step` does, rather than nesting a run. The elaborator
   then handles a long chain of folded calls under `Succ` the way the
   kernel does, and a blocked pair inside it can wait (F1, S; unifier, so
   Opus).
2. Add `Succ (Succ (withProof (0)))` to the fields matrix. It is the
   only shape that reaches the lazy path's new `assign` arms with a call
   still in the other side, the lane's second doubt (F3a, S).
3. Add an accept example that solves an unknown through the unfolding,
   and a deep chain (a `decreasing` count returning `Succ (count m)` at a
   few thousand). They cover the unifier's branch and pin F1 (F3b, F3c, S).
4. Rescope SW-2235: its F1 (the "once a side" comment) went with the
   removed rule. Its F2 matrix terms (`valueOf`, `outerV`/`wrap`) are still
   worth adding (F3d).
5. Note on `compare_lazily` (or on `Value::NatAdd`) that the `rest` it
   hands to `assign` can be `k + call`, outside `NatAdd`'s stated
   invariant (F2, S).

| # | Finding | Severity | Confidence | Size |
|---|---|---|---|---|
| F1 | The unifier's new branch nests a run per level (Rust recursion, no postponement), where `conv` pushes onto its work list | low | high | S |
| F3 | Test gaps: lazy `assign` with a call in `rest`; the unifier solving through the unfolding; a deep chain; SW-2235's terms | low | medium | S |
| F2 | `compare_lazily` builds `NatAdd(k, call)`, which `NatAdd`'s documented invariant excludes; harmless today | low | high | S |

## Answers to the brief's questions

**Q1. Is everything newly accepted definitional, and do all four places
agree, transitivity included?**

Yes.

- **Definitional.** In every place, a "true" from the new code comes from
  comparing `unfold_folded(x)` with `rest`. `value::unfold_folded` runs the
  definition's case tree on its arguments (`value.rs:2489-2537`) through
  `body_seen`. The reference does the same through `seen` and `eval_tree`
  (`reference.rs:360-386`). That's delta. Nothing else changes: when the
  base isn't folded, or its tree is stuck, every place still answers
  "different".
- **Which inputs reach `assign`.** After the shared `Succ`s are gone, the
  base `x` has none left. The other side then either has some left or is a
  number. So `rest` is never a bare base, which matters for Q3.
- **Glued against unglued, lazy against eager.** I went through every arm
  of `compare_lazily`'s match against what `compare` does with the calls
  forced:
  - Two bases, both with no `Succ`s left, go to `same`.
  - A call with no `Succ`s left is unfolded a step. The new `assign` arms
    come after both call arms, so the `x` they hand on is never a call.
  - A non-call base `x` with no `Succ`s left against `k + call` (`k ≥ 1`)
    goes to `assign(x, k + call)`. Eager `compare` would first force the
    call, giving `k' + base'` with `k' ≥ k`, and then reach
    `assign(x, k' + base')`. That's the same `x`, against a value equal to
    the lazy `rest`.
  - The pushed task compares the two lazily, and a call compares as its
    unfolding. So the answers agree.
  - The last arm (`_ => false`) is now reached only by `0` against
    `k + something` with `k ≥ 1`, which is right in both.
- **Unglued.** It is the same `conv_step` with no calls in the values. The
  folded base is reached directly and unfolded by the same `assign`.
- **Reference.** It unfolds a folded base and returns "different" if the
  unfolding didn't move, using the same `ptr_eq` test as its folded rule.
  `value::unfold_folded` returns `None` in exactly that case. A step that
  moves to another folded call which is stuck returns that call in both.
  Either way the next round's `assign` answers "different".
- **Unifier.** It uses `value::unfold_folded` itself and, after
  unfolding, unifies the result with `v` from the top. That does what
  `conv` does, and more where an unknown can be solved.
- **Transitivity.** Folded bases under `Succ` are now opened in every
  mode, so equal means "equal once folded calls are unfolded" everywhere.
  That was the missing piece in SW-2234's F3 counterexample. The new matrix
  terms, `Succ (withProof (outerN 0))` and `Succ (withProof 1)`, are that
  counterexample, and `compared_alike` checks transitivity on them.

**Q2. Does it terminate and stay within budget?**

Yes.

- **Kernel and `conv`.** Each firing of `assign` pushes one task. Each task
  costs a budget step in `conv_with`. Inside `unfold_folded`, every step it
  takes runs the machine, which steps the budget. A chain of firings follows
  a chain of real unfoldings, each a step of a definition the checker
  accepted as terminating. So a long chain ends in E-RESOURCE, never a hang,
  and `conv` uses no Rust stack for it.
- **Infinite loops.** `unfold_folded` returns `None` when a call doesn't
  move. A call that moves to a stuck folded call ends on the next round,
  which gets `None`.
- **Unifier.** It terminates too, since every `run` task steps the budget
  and `Budget::step` checks the stack floor (`budget.rs:617-623`). But it
  recurses (F1).
- **Reference.** It recurses through `conv_in` as before, and is used only
  in tests.
- **Cost.** The new work happens only where the answer used to be
  "different", as the lane says. The lane's AoC timing (68.3 s against
  67.9 s) agrees.

**Q3. Are the lane's two doubts real problems?**

No, neither is.

1. **The unifier unfolds before `plus_rule` sees a folded stuck sum.**
   `plus_rule(x, v)` looks for a stuck sum on either side:
   - On `x`, `stuck_sum` needs a `Neutral` headed by `nat_add_rule`'s
     definition with exactly two applications. `Nat.add` is never folded:
     `folds` is dictionaries, `decreasing` definitions and theorems
     (`def.fold || def.theorem`), plus `Quot.lift` leaves and
     `folds_mul`, which needs `Native::Mul`. A call field has a projection
     in its spine.
   - On `v`, `v` is `from_view(k, other)`, which is never a bare neutral
     (Q1). So `stuck_sum(v)` is always `None` here.

   So `unfold_folded(x)` is `Some` only where `plus_rule` would have found
   nothing, and the order changes no answer. Where the unfolding *is* a
   stuck sum, the nested run reaches `plus_rule` at the top of
   `unify_step`, which is strictly better than before.
2. **On the lazy path, a base that isn't a call goes to `assign` with
   glued calls still inside the other side.** That's fine for
   correctness:
   - `compare_lazily` has one caller, `conv_step`.
   - Its `assign` either answers "different" for a non-folded `x`, or
     pushes `(unfold(x), rest)` for `conv`, which compares a call as its
     unfolding.
   - "Different" is right whatever the calls in `rest` compute to. A base
     with no `Succ`s that isn't folded is a stuck neutral, such as a
     variable, a stuck `case` or a stuck `J`. It never equals a `Succ` or a
     number, however many more `Succ`s the calls give.

   The doc comment on `compare_lazily` states this condition correctly.
   The only cost is a value outside `NatAdd`'s invariant (F2). No matrix
   term reaches this arm with a call in `rest` (F3a).

**Q4. Was removing SW-2211's rule safe in every case it covered?**

Yes. The rule fired on a glued call against something `nat_like`. It
forced the call and compared again from the top, where the only rules
before numbers that could act on the result are the folded rule and the
numbers' rule itself.

`compare_lazily` now does the same on its first turn. The call side has no
`Succ`s, so the call arm forces it. Then, on what comes out:

- **A folded call** has no `Succ`s, so it now goes to `assign` and is
  unfolded by the same `unfold_folded` the top's folded rule used.
- **Something `nat_like`** is stripped and compared as before. A folded
  base under it is now opened, which the rule never did.
- **A stuck value** is "different", as before.

With the shortcuts disabled, eager `compare` forces the call in
`view_with`, then reaches the same `assign`.

SW-2234's example, `wrap 0` against `0` with `def wrap (x) := outerV x`, in
the glued mode:

1. `compare_lazily` sees `wrap 0` as a call with no `Succ`s against `0`,
   and forces it to the folded `outerV 0`. `outerV` is `decreasing`, so it
   is marked folded (`decreasing.rs:1197`, `mark_folded`).
2. `outerV 0` isn't a call and has no `Succ`s. The new arm hands
   `assign(outerV 0, 0)`.
3. `unfold_folded(outerV 0)` runs the tree to its leaf `valueOf 0`, a glued
   call. Forcing that gives `(countDown 0).value`, which `folded_call`
   rejects, since it excludes fields. So the result is kept as the call
   `valueOf 0`, and `(valueOf 0, 0)` is pushed.
4. `compare_lazily` forces `valueOf 0` to the field
   `(countDown 0).value`, with no `Succ`s. Then `assign` runs
   `unfold_folded`, which opens the field through `is_folded`'s
   call-field arm and gives `0`. `(0, 0)` is pushed, and the answer is
   "equal".

The other modes reach the same answer:

- **Shortcuts disabled:** the same steps, eagerly.
- **Unglued:** `wrap 0` is `outerV 0` at once, and the top's folded rule
  unfolds it.
- **Reference:** unfolds at the top.

The rule's two firings in SW-2234 are now two rounds of `compare_lazily`'s
loop and `assign`, and both are bounded as in Q2.

**Q5. Is the `core.md` clause accurate?**

Yes. "A base left with no `Succ`s against a different count of them, or
against a number, is unequal unless it's a folded call, which is unfolded
and compared again" matches `compare_with`'s and `compare_lazily`'s
`assign` arms exactly:

- "against a number" covers the case where both counts are zero;
- the example `Succ (id (f 0))`, glued or not, is the old rule's case
  folded in.

The clause is now a long parenthetical inside a longer sentence. That's a
readability nit, not worth its own finding. `core.md` doesn't describe the
unifier, so its omission there is right.

**Q6. Do the tests cover the change?**

Partly (F3):

- **The matrix.** The three new terms, compared against every depth-2 term
  in five modes, cover glued, unglued, kernel, eager and reference agreement
  for a folded base with no call in `rest`. The explicit "is `2`" asserts
  pin the fix.
- **The example.** It goes through the elaborator's unification: `rfl`
  unifies the two sides, and `conv_now` isn't on that path. It also goes
  through the kernel.
- **Gaps.** Three shapes aren't covered: the lazy arm with a call in
  `rest`, an unknown solved through the unfolding, and a deep chain.

## Findings

### F1 (low, high confidence): the unifier nests a run per level

`crates/elab/src/unify.rs:1377-1381`:

```rust
if let Some(x) = unfold_folded(g, x)? {
    return nested(g, || run(g, vec![Task::Values(level, x, v.clone())], mode));
}
```

Each level of folded call under `Succ` adds a Rust frame chain:
`nested` → `run` → `unify_step` → `native::compare` → this closure →
`nested`. `conv_step` instead records the pair and pushes it onto its work
list. Two consequences:

- **Depth.** Take `def count (n: Nat): Nat decreasing n := match n with |
  Zero => 0 | Succ m => Succ (count m) [decreasing := omega]` and
  `theorem t: count 5000 = 5000 := rfl`. The kernel's `conv` checks it
  iteratively. The elaborator's unification recurses about 5000 levels
  deep, and at some depth the stack floor turns that into E-RESOURCE. It is
  safe (D2543: limits fail), but the elaborator rejects what the kernel
  would accept, and it was a plain mismatch before. I haven't measured the
  depth at which this bites.
- **Postponement.** `nested` clears `attempt.waiting`, so a pair inside the
  unfolding that is blocked on an unknown can't wait for the queue
  (docs/proposals/postponement.md). It fails instead. A pushed task would
  be postponed like any other.

The `plus_rule` branch below it nests in the same way, but that is
pre-existing and builds its own work list.

Recommended change (S): do what `conv_step` does. Keep an
`Option<(Value, Value)>` that the `assign` closure fills, return `true`
from the closure, and after `native::compare` returns, push the pair onto
`work`. `same` already borrows `work` mutably, which is why the lane
nested, but the `Option` sidesteps that. Test with F3c's deep chain. This
is the unifier, so it goes to Opus under D2506.

### F2 (low, high confidence): `NatAdd(k, call)` outside its invariant

`crates/core/src/native.rs:855-860` builds `from_view(k, Some(call))` for
`rest`, which is `Value::NatAdd(k, call)`. `Value::NatAdd`'s doc
(`value.rs:31-32`) says its base is "an `x` not built from numbers", but a
glued call may compute to one.

This is harmless today:

- `compare_lazily`'s one caller only compares `rest`;
- `view_to_call` looks through a call, and `view_with` forces one;
- the value is never quoted or stored.

But the next caller of `compare_lazily` with an `assign` that keeps `rest`
would store a non-canonical number. One that solves an unknown with it, as
the unifier's `assign` does, is the obvious case.

Recommended change (S): add a line to `compare_lazily`'s doc saying that
the other side handed to `assign` may be `k + call`. Alternatively, relax
`NatAdd`'s comment to allow a glued call as the base. Code changes aren't
worth it.

### F3 (low, medium confidence): test gaps

`crates/driver/tests/proofs/proof_equivalence.rs` (`fields_of_calls_are_compared_alike`)
and `examples/accept/succ-of-folded-call.sw`:

a. **The lazy `assign` with a call in `rest`.** The matrix's terms go to
   depth 2, plus three, so no pair has a folded base under fewer `Succ`s
   than a call under more. Add `Succ (Succ (withProof (0)))` (it is `2`).
   Against `Succ (innerN (0))` it gives `assign(innerN 0, 1 + withProof 0)`
   in the glued mode, while eager and unglued see it with the call
   already gone. The matrix's agreement check then covers the lane's second
   doubt.
b. **The unifier solving through the unfolding.** The example needs the
   new unifier branch (`rfl`'s check goes through unification, not
   `conv_now`), but no unknown is solved there. Add a case where the
   other side has one, for instance an implicit argument `n` solved from
   `Succ (innerN 0)` against `Succ (Succ n)`. Before the change that was a
   mismatch.
c. **A deep chain.** Add F1's `count` at a depth of a few thousand. Checked
   by the kernel and by elaboration, it pins F1. Size it to stay fast.
d. **SW-2235.** That ticket's F1 asks to reword the "this happens once a
   side" comment, which went with SW-2211's rule. Its F2 terms are still
   missing: `valueOf x := (countDown x).value`, and a `decreasing`
   definition whose leaf is `valueOf`. They would now go through the new
   `assign` path (Q4's trace).

Recommended change (S): one lane for a, d and the F2 comment; b and c
with F1.

## Checked and sound

- **The `unfolded` slot in `conv_step`.** `assign` is called at most once
  and only as `compare`'s return value, so the slot holds at most one pair,
  pushed only when the answer is `true`. `same` and `assign` are each
  `FnOnce`, and only one of them runs.
- **Mode.** The pushed pair runs in the comparison's current mode. Shortcut
  mode is stricter on proof fields, so an unfolding compared there can only
  say "equal" where the normal mode would. The reference passes `mode`
  through in the same way.
- **`CallMemo`.** The memo is untouched. No new path records anything, and
  the pairs pushed are compared like any others.
- **Opaque, pending and axioms.** `is_folded`, `folded_call` and the
  reference's `is_folded` all need `body_seen`/`seen`, so a hidden or
  missing body is never unfolded by the new code.
- **`folds_mul`.** `mul k x` under `Succ` unfolds to `add x (mul (k-1) x)`,
  stuck on `x`, and then answers "different" on the next round. That's
  right.
- **The removed rule's comment (SW-2234 F1)** is gone with the rule. The
  new comments in `conv_step`, `compare`, `compare_lazily`, `reference.rs`
  and `unify.rs` say why rather than what, and are accurate.
- **The unifier's meta case comes first.** An unknown base is still solved
  with `v` before any unfolding, so a folded call is never unfolded where
  an unknown could take it by name.
- **`check_work.rs`** mentions `compare_lazily` only in a comment. Its
  SW-1153 bound isn't affected, since the new work happens only where the
  answer used to be "different".

## Status of earlier reviews' findings in scope

- **`docs/research/rust-codebase-review.md` (1 Nov).** It has no finding on
  the numbers' path, conversion's folded calls or this unifier rule.
  `architecture-review.md` has none either.
- **SW-2234's findings:**
  - F1, the comment: moot, since the comment was removed with the rule.
  - F2, the matrix terms: open, as SW-2235 (F3d here).
  - F3, folded calls under `Succ`: fixed by this change.
- **SW-2158's F1** (`unfold_folded` doesn't force solved unknowns between
  levels): not touched, so still as that review left it.

## Tickets to file

- **Lane A: Opus, about 45 min (unifier, D2506).** F1, with F3b and F3c:
  - in `unify.rs`, push the unfolded pair onto `work` instead of nesting a
    run;
  - add the unknown-solving accept example and the deep `count` chain.

  Tests: `task test:one -- succ-of-folded-call` and the new example(s), and
  the `hash_stability` snapshot for new examples. It changes what the
  elaborator accepts (more), not the kernel.
- **Lane B: Sonnet, about 30 min.** F3a, F3d and F2:
  - add `Succ (Succ (withProof (0)))`, `valueOf` and `outerV` (or `wrap`)
    to the fields matrix;
  - add the `compare_lazily` doc line.

  This replaces SW-2235's scope: drop its F1 and keep its F2. Test: `task
  test:one -- proof_equivalence`. The matrix grows by the square of the
  term count, so check that it stays fast.

## Calls I made

- I made F1 low, not medium. It loses completeness only at depth, and the
  failure is a clean E-RESOURCE. The kernel isn't affected.
- I suggested rescoping SW-2235 rather than filing a new matrix ticket,
  since the terms overlap.
- I kept `core.md`'s long parenthetical as a nit, not a finding. SW-2236 is
  looking at the pattern behind these clauses and may rewrite it anyway.

No D questions.
