# SW-2158: review of merge `8e952180a` (SW-2126, glued leaf unfolding)

A review of SW-2126, which fixed F1 and F4 of
[SW-2125-folded-call-fields.md](SW-2125-folded-call-fields.md). It changes
what kernel conversion accepts, so it gets an Opus review (D2364). I only
read code: no builds or runs. Read: `git show 8e952180a -m --first-parent`;
in `crates/core/src/value.rs`, `run`, `force`, `force_now`, `force_solved`,
`force_call`, `needs_forcing`, `unfold_now`, `folds`, `folded_call`,
`is_folded`, `folded_parts`, `unfold_for`, `unfold_field_for`,
`unfold_folded`, `branch`, `eta_fields`, `walk_tree`, `conv_step`'s folded
branch, and `resume`'s `Unfolding`, `Unfolded`, `Replay`, `ReplayElim`,
`ProjForced`, `FoldedField`, `Scrutinee` and `LiftForced` arms;
`native::compare_lazily` and `view_to_call`; `reference.rs`'s `force`,
`unfold`, `unfold_folded` and `is_folded`; the callers of `unfold_folded`
in `elab` (`cases.rs`, `interfaces.rs`, `omega.rs`, `search.rs`,
`unify.rs`); the new tests; `match-call-field.md` §10; and tickets SW-2126,
SW-2127 and SW-2157.

## Summary

The change is sound, and it makes glued evaluation agree with unglued and
the reference where it didn't before. Every step it adds is a delta step:
it forces a glued call, which runs that definition's case tree, or it
unfolds a folded call, which runs that one's. Both go through `unfold_now`
or `unfold_for`, so a hidden opaque body or a member of the group being
checked still never unfolds. Unglued evaluation takes these same steps: the
fuelled helper isn't glued there, so its leaf `g y` arrives at
`Frame::Unfolding` as a folded call and is unfolded. The reference's
`unfold_folded` recurses through `force` to the end. So the equalities the
kernel now accepts, such as `outerN 2 = 1`, are ones the other two
evaluators already accepted. This closes a D3030 gap, where glued
evaluation was incomplete; it opens none. The loop can't run without
spending budget: each turn passes through `run`, which steps the budget,
and the stack stays the same depth. A call stuck in its own case tree still
stops it, through the `ptr_eq` check. `Force` → `Return` in the default arm
changes nothing: `run` returns at once any value that `needs_forcing`
rejects. `ReplayElim` names the same field as `FoldedField` in every case
but one. The one gap is `unfold_folded`, which forces glued calls between
levels but not solved metavariables, as `Frame::Unfolding` and the
reference do (F1). That affects naming and elaborator heuristics, not what
conversion accepts.

Top recommendations:

1. Make `unfold_folded` force anything `needs_forcing` accepts between
   levels, not only `Value::Call`. Then a solved metavariable at a leaf is
   followed to the end as in `Frame::Unfolding` and the reference, and
   `ReplayElim` names what `FoldedField` names (F1). Fix the
   `Frame::Unfolding` comment to say it handles metavariables too.
2. Do SW-2127 (a matrix row for the kernel's own glued mode) next, and add
   this change's `outer`/`outerN` terms to it. Today the kernel's glued
   mode is tested only end to end, by four `rfl` theorems (F2).
3. Add matrix terms for the other chain shapes: a theorem ending in another
   theorem (`reachableIff`'s shape), a dictionary whose body is a glued
   call, and a helper whose leaf is a `Quot.lift` definition (F2).
4. Keep SW-2157 a separate lane. It's a gap in numeric comparison that all
   three evaluators share, not part of this change. When it lands, add a
   `Succ (outerN 0)` term to the matrix.
5. No cost action now. If a profile ever shows `unfold_folded` forcing
   under `conv_step`, look at F3.

Findings: high 0, medium 0, low 3 (F1-F3).

## Findings

| # | Where | What | Severity | Confidence | Fix |
|---|---|---|---|---|---|
| F1 | `value.rs:2518` (`unfold_folded`), `value.rs:1786` (`Frame::Unfolding`'s comment) | `unfold_folded` forces only a glued call between levels, not a solved metavariable. So a meta leaf whose solution is a folded call stops there: `ReplayElim` names `(f x).i` where `FoldedField` computes the field, and a `case` on it stays stuck in the elaborator | low | medium | S |
| F2 | `proof_equivalence.rs:227`, `call_fields.rs:350` | The kernel's glued mode (`glue` and `kernel` on) has no matrix row: only the four theorems of `a_folded_call_ending_in_another_computes_to_the_end` reach it. The matrix has only decreasing-to-decreasing chains | low | high | S-M |
| F3 | `value.rs:2518-2523`, `value.rs:1786-1789` | `unfold_folded` now forces every glued call a folded call unfolds to, where conversion used to keep it lazy. `Frame::Unfolding` allocates one extra box per glued unfolding | low | medium | none now |

## Details

### F1. `unfold_folded` skips solved metavariables between levels

`Frame::Unfolding`'s new arm tests `needs_forcing`: a glued call *or* a
solved metavariable. The matching block in `unfold_folded` tests
`matches!(next, Value::Call(..))` only. The reference forces between
levels (`unfold_folded(g, force(g, next)?)`, `reference.rs:382`), so it
does both.

**Reaching it.** A folded call's case tree can return a variable whose
value is a solved metavariable that was never forced: a spine argument
built before the meta was solved. `run` hands back `Term::Var`'s value as
it is. Example: a `decreasing` `pick (x: Nat) (d: Box): Box` whose `Zero`
leaf is `d`, applied to `?m := inner 0`.

- `Frame::Unfolding` (a projection, through `FoldedField`): forces `?m`,
  sees `inner 0` is folded, unfolds it, and projects the record. The
  field is the number.
- `ReplayElim` (the same projection, replayed on a metavariable solved to
  `pick 0 ?m`): `unfold_folded` returns `Some(?m)`. `force` gives
  `inner 0`, a non-meta neutral, so the new guard names `(pick 0 ?m).value`.
- In the kernel's non-naming mode it projects `inner 0` without unfolding
  it, which gives the call field `(inner 0).value`. That's lazily equal,
  but a `case` on it doesn't step (SW-2125 F1's `branch` → `stuck_tree`
  path).

**What it affects.** Conversion still decides these, because `conv_step`
forces what `unfold_folded` returns and unfolds it again if it's folded.
So no equality changes, and the kernel never sees metavariables. What does
change, in the elaborator only, is how the field reads, whether a `case`
on it computes, and what `cases.rs`'s chain walks (`cases.rs:1288`, `1505`,
`1720`) see. This is F1's pattern from SW-2125, still open for one input.

**Change.** In `unfold_folded`, replace `matches!(next, Value::Call(..))`
with `needs_forcing(g, &next)`, and keep the rest. Correct the
`Frame::Unfolding` comment (`value.rs:1779-1785`) and the §10 bullet to say
that a solved metavariable is forced and looked at again too. That is new
behaviour in unglued elaboration as well. It's right, since it's what the
reference does, but it isn't mentioned. Add a `call_fields` test for the
`pick 0 ?m` shape. Size S, Opus or Sonnet (core evaluator, but a one-line
change with a clear test).

### F2. Test coverage of the kernel's glued mode

The changes to `Frame::Unfolding` and `unfold_folded` aren't gated on
`names_folded_fields`, so they act the same in the elaborator's glued mode
and the kernel's. The matrix's `GLUED` is the elaborator's mode (naming
on). The kernel's mode is reached only through admission, by the four
theorems in `a_folded_call_ending_in_another_computes_to_the_end`. That
test can fail, and it did before the fix, but only in the "accepts"
direction, for four pairs. SW-2127 (backlog) adds the kernel row.

The matrix's new terms cover one shape: a `decreasing` definition ending
in another `decreasing` definition. These shapes are untested:

- a theorem whose proof is another theorem's call (`reachableIff`);
- a dictionary whose body is a glued call that computes to another
  dictionary;
- a helper whose leaf is a lift-leaf definition (`Map.foldLeft`). Forcing
  it now gives `Neutral(Def foldLeft)` stuck on its lift, which
  `Frame::Unfolding` then unfolds through the lift. Unglued and the
  reference do the same (checked below), but nothing tests it;
- a metavariable leaf (F1).

**Change.** Fold into SW-2127: add `kernel: bool` to `How` and the row
`How { kernel: true, ..GLUED }`, and add the shapes above to
`FIELDS_PROGRAM` where they can be built. Size S-M, Sonnet.

### F3. Cost

- `unfold_folded` (`value.rs:2518`). Before, a glued call that a folded
  call unfolded to went back to conversion as it was, to be compared
  lazily: by arguments against a call of the same definition (`CallMemo`),
  or by `compare_lazily` a `Succ` at a time. Now it's always forced first.
  The result is cached in the call's shared `Unfolding` and the call is
  kept, so it's never forced twice. Conversion would force it next in
  almost every case anyway. The one exception is two calls of the same
  helper with equal arguments, behind folded calls whose own arguments
  differed, and the helper's arguments usually include the outer ones. So
  the extra work is rare. The other callers (`cases.rs`, `interfaces.rs`,
  `search.rs`, `omega.rs`) also pay one forcing per glued result. On AoC
  scale data, `Map` folds are lift-leaf calls, which aren't `fold` or
  theorems. They reach this block only through `is_folded`'s lift case, on
  a quotient that isn't a `Quot.mk`, so on stuck values, where forcing
  stops early.
- `Frame::Unfolding` (`value.rs:1786`). The old default arm already forced
  the value, so the tree work is the same. What's new is one `Box` and one
  extra frame push per unfolding whose result is a glued call, which is
  every `decreasing` definition taken apart while gluing. That's small next
  to running its tree. `Force` → `Return` saves one machine step.

The lane reports AoC at 0 errors in 62 s. No change now.

## Answers to the brief's questions

1. **Soundness.** Every new equality is a genuine definitional one, and the
   one the other evaluators give.
   - The new steps are `force` on a glued call (`force_call` →
     `unfold_now(.., false)`, which checks `hidden` and needs a body) and
     `unfold_for` on a folded call (`folded_call` needs `body_seen`). Both
     are delta steps.
   - Unglued, the helper's tree runs inside `f`'s, and its leaf `g y`
     reaches `Frame::Unfolding` folded and is unfolded. The reference's
     `unfold_folded` recurses through `force`. So glued now takes exactly
     the steps they took (D3030).
   - The lift-leaf variants agree too. If the helper is itself `lift_leaf`,
     or its leaf is a lift-leaf call, all three evaluators get the stuck
     `Neutral(Def ..)` and then unfold it through the lift (`unfold_for`
     and `eval_tree` with `fold_lifts = false`).
   - The kernel accepts more only where glued conversion used to stop
     early: `outerN 2 = 1`, where `compare_lazily` forced the helper's call,
     got the folded `innerN 0`, which isn't a number, and answered no.
     That's the incomplete direction of D3030, now closed.
2. **Termination and budget.**
   - Each re-entry of `Frame::Unfolding` passes through `run`'s loop, which
     calls `budget.step()`. Forcing always returns a value `needs_forcing`
     rejects (`Unfolded` and `Replay` force until it does), so there is at
     most one forcing per level. Each further level runs a case tree.
   - The frame is popped before it's pushed again, so the stack's depth
     doesn't grow along a chain. A chain that never ends fails on steps,
     not depth (D2543).
   - A call stuck in its own case tree: `unfold_for` passes the same
     `call` Rc to the frame and to `Stuck`, so `stuck_tree`'s result
     passes the `ptr_eq` test and goes to `next`. A helper stuck in its own
     tree returns `Neutral(Def helper)`, which isn't folded (unless
     lift-leaf: then it's unfolded once through the lift, and the result
     isn't folded). No loop.
   - `unfold_folded`'s loop: each turn runs `run` at least once, and goes
     on only while the value `is_folded`.
3. **`Force` → `Return`.** It's correct. The default arm is reached only
   when `needs_forcing` is false: not a solved meta and not a call. On such
   a value, `run`'s `Control::Force` is `Control::Return` (an unsolved
   meta and `other` both return at once, and `Chars` isn't expanded by
   `value.rs`'s force). Nothing can skip forcing, because the
   `needs_forcing` arm comes first. The step count drops by one per
   unfolding. That's deterministic and harmless.
4. **`ReplayElim`'s guard.** It names the same as `FoldedField` in every
   case but F1's:
   - stuck in its own tree: `unfold_folded` gives `None`, and both give
     `project(f x)`;
   - ending stuck in another folded call `g y`: both name `(f x).i`;
   - a glued call: both get the forced value. A neutral is named, and a
     constructor is projected;
   - an unsolved meta: both give `?m.i`;
   - the kernel or unglued: both project the unfolding;
   - a solved meta at a leaf whose solution is a folded call: they differ
     (F1).
   `ReplayElim` on a *call field* `(f x).i` computes it, where
   `ProjForced` keeps `(f x).i.j`. That predates this change and doesn't
   involve `FoldedField`.
5. **Cost.** A little more forcing in `unfold_folded`, one box in
   `Frame::Unfolding`. Neither is on a hot path for concrete `Map` folds
   (F3).
6. **Tests.** Not by a matrix row. The kernel's glued mode is reached only
   through admission of the four theorems in `call_fields` (F2, SW-2127).
   The solved-metavariable test does exercise both new paths
   (`ReplayElim` and rule 2 via `force_solved`) and would have panicked
   before.

**SW-2157.** Keep it separate. It's a missing equality in all three
evaluators alike (`Succ (innerN 0) = 2`): `view_to_call` and `view` don't
unfold a folded call they reach under `Succ`. It isn't a glued/unglued
disagreement, and fixing it means changing `compare_lazily`,
`compare_with`'s callers, the reference and the unifier together. SW-2126's
`unfold_folded` block fixes the top-level instance of the same shape for
glued conversion. Once SW-2157 lands, conversion would no longer need that
block, but the other callers of `unfold_folded` still would, so keep it.
Add a `Succ (outerN 0)` term to the matrix in that lane.

## Checked and sound

- `needs_forcing` is exactly the set of values `run`'s `Force` changes, so
  splitting the default arm on it loses nothing.
- Every new forcing goes through `unfold_now(.., false)` or `unfold_for`.
  Opaque bodies (`hidden`), pending group members (no body) and natives
  behave as before. Nothing changes while a program runs (`folds` and
  `folds_on_lift` are off then, and gluing is off).
- `eta_fields`'s `force_solved` runs only when naming is on (elaborator,
  glue on). It stops at glued calls, so a meta solved to a glued call keeps
  the existing projection-of-forced behaviour (SW-2125 F4 noted this). With
  `J`/`Proj` in the spine it forces fully, and `forced` is then the
  unfolding of the folded call it finds, so the name is right.
- `walk_tree`'s `eta_fields` call can't name through a meta. If the
  meta's solution is folded, `force` gives the folded call, and
  `!folded_call` excludes it first.
- The doc claim on `eta_fields` ("`forced` ... isn't a folded call that can
  still compute; at most one stuck in its own case tree") holds for all
  three ways into `branch`: run's `Tree` arm, `Scrutinee` and
  `ScrutineeReady`.
- `ReplayElim`'s `J` arm now forces too, so a glued call can't reach its
  `panic`. (Its lack of an erased-proof arm, which `JForced` has, predates
  this change and can't be reached: `ReplayElim` runs only on
  metavariables, so only while elaborating.)
- `unfold_folded`'s new block is gated on `fields.is_empty()`. The field
  branch already forces and unfolds again, so nothing is missed there.
- The solved-metavariable test's environment indexing is right
  (`Term::Var(0)` is the unforced meta).
- The lane reported `snap:hashes` unchanged, so the `cases.rs` chain walks,
  which now see past a glued helper, changed no std elaboration.

## 1 Nov review (rust-codebase-review.md), findings in scope

- **4.1, manual restoration:** still open (SW-2113). Untouched here.
- **4.4, large files:** `value.rs` is 4,831 lines, up from 4,781. The
  folded-call machinery (`Unfolding`, `FoldedField`, `ReplayElim`'s guard,
  `unfold_folded`, `eta_fields`'s naming) now has three sites that must
  agree on "followed to the end", and F1 is one of them drifting. A shared
  helper, "what this folded call computes to, to the end", used by
  `unfold_folded` and mirrored by `Frame::Unfolding`, would keep them in
  step. That's worth doing when the module is next split, not alone.
- **2.2, relationships between implementations:** the matrix is the right
  tool here, and this change used it well. The kernel row is still missing
  (F2).
- **2.3, resource exhaustion:** the new loop fails on the step limit, as
  required.

## Tickets to file

- **Lane A (Sonnet, 30-40 min): `unfold_folded` forces solved metas
  between levels.** F1: `needs_forcing` in place of the `Value::Call`
  test, a `call_fields` test with a meta leaf (`pick 0 ?m`), and comment
  and §10 fixes. Targeted tests: `call_fields`, `proof_equivalence`.
- **Add to SW-2127 (Sonnet, +20 min):** the kernel-glued row, plus F2's
  chain shapes (theorem → theorem, dictionary → glued call, lift-leaf
  leaf) in `FIELDS_PROGRAM`.
- **SW-2157 as filed (Opus):** add a `Succ (outerN 0)` term to the matrix.

## Questions for Matt

None.

## Calls I made

- F1 is low, not low-medium. No equality changes (conversion recovers),
  only elaborator naming and heuristics, and it needs a meta at a leaf.
- I recommend Sonnet for F1's fix despite its being in the core
  evaluator. It's a one-line change on a path this review has traced, with
  a clear test. Escalate if the test shows anything unexpected.
- I didn't move the ticket. The review rules say not to edit
  `board/tickets.json`, so the orchestrator moves it.
