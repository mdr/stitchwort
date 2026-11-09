# SW-2554 review: a `match` that refines nothing keeps the goal as written

Independent Opus review (D2364: the change alters the terms the elaborator
generates), of `lane/SW-2554` at e0f9cb4a3. Read only: nothing built or run.

## Summary

The change is sound. When the usual occurrence test refines nothing (no
scrutinee occurs in the unfolded goal, and the goal mentions no copied
variable in either form), the old motive was the unfolded goal shifted under
the new binders, and the new one is the folded read-back of the same value
shifted the same way. Both are read-backs of one `Value`, so they are
convertible, and the kernel gets a motive that is, if anything, closer to the
declared statement than before. I found no case where an arm should have been
refined and now isn't: every input to the refinement decision is computed
exactly as before, and the new path is taken only when that decision was
"refine nothing".

The real risk is elaboration rather than soundness. Inside the arms the goal
is now the folded one, the goal the proof had before the `match`, so a proof
that worked only because the `match` had unfolded the goal can now fail.
std still checks (the hash snapshots were regenerated), but AoC and the
roguelike were not checked, and 948 std hash changes mean they re-elaborate
on top of new std terms anyway. The `W-MATCH-NOT-FOUND` notes are never
false, but the new "computed" note uses a string test, which makes it noisy
in some cases and leaves it out in others.

Top recommendations:

1. Check AoC and the roguelike against this change before pushing (cached
   checks re-run everything that depends on the changed std hashes), in the
   next compute window or as part of the daily tier (F1).
2. Call `undo::recovered` after the recoverable error in `unrefined_goal`,
   as its contract asks (F2).
3. Decide the "computed" note by term occurrence, not substring, and keep
   the computed expression visible when the goal falls back to its unfolded
   form (F3, F4).
4. Read the goal folded once per `match`, not twice (F5).
5. Add a goals example that pins the boundary: a copied hypothesis that the
   goal mentions keeps today's motive (F6).

| # | Finding | Severity | Confidence | Size |
|---|---|---|---|---|
| F1 | AoC and roguelike unchecked; proofs that relied on a `match` unfolding the goal may now fail | medium | medium | S (a run) |
| F2 | `unrefined_goal` recovers from a size error without `recovered(cx)` | low | high | S |
| F3 | The fallback note mixes a written expression with an unfolded goal, and loses the computed expression | low | high | S |
| F4 | The "computed" note is gated on a substring test | low | high | S |
| F5 | The goal is read back folded twice, adding steps to every such `match` | low | high | S |
| F6 | No test of the copied-variable boundary | low | medium | S |
| F7 | A scrutinee variable erased by unfolding stays visible in the arms' goal | low | low | none or S |

## Details

### F1. AoC and roguelike proofs were not checked (medium, medium confidence)

`crates/elab/src/matching.rs:1407-1410`. Inside the arms the goal used to
be `eval(quote(goal))`, the normal form re-evaluated, and is now
`eval(quote_folded(goal))`. Anything that forces sees the same thing either
way. What can differ is code that reads the goal's shape without forcing, or
reads it back folded and matches it syntactically:

- **As-written paths** (`rewrite/as_written.rs`, `matching/as_written.rs`
  for nested matches, `auto::decide_as_written`). They now see the calls the
  user wrote rather than bodies. They all fall back to the unfolded search
  (rewrite, nested `match`) or run after it (`decide_as_written`), so they
  can only find more, and what they find goes through the same motive
  checks. Likely to break an existing proof: very low.
- **Unification and implicit solving.** `double ?k =?= double n` now solves
  by arguments first, where before it compared `?k + ?k` with `n + n`. The
  glued unifier already does this for every goal outside a `match`, which is
  the same folded goal. Likely to break a proof: low.
- **`omega`**: forces the goal (`omega.rs:279`) and identifies atoms
  syntactically with a `conv` fallback (`omega.rs:2376-2392`), so it is
  unaffected. **`rfl` / `E-REFL`**: `conv`, unaffected apart from step counts.
- **Head-shape checks that stop at a glued call** (`force` variants that
  keep `Value::Call`, `value.rs:864`): an anonymous constructor or a
  projection checked against `MyProp x` rather than its unfolding `A ∧ B`.
  These are again the cases every proof already meets outside a `match`.

So the regression path is narrow: a proof inside the arms of a `match` that
refines nothing, which worked only because the arms' goal was unfolded, as an
accidental `unfold`. It can't make the kernel accept something wrong, and
any break is a loud elaboration error. std passes, so the risk lies in AoC
and the roguelike, which have many proofs written against whatever goal the
arms showed. Kernel work in the arms may also shift: bodies elaborated
against folded goals can need the kernel to unfold where it used to compare
normal forms. That is step-counted, so deterministic, but a declaration near
its limit could tip over.

Recommendation: before this reaches GitHub, run the AoC and roguelike checks
(the cached check re-elaborates everything that depends on the 948 changed
std hashes, so it is close to a full run). This is a broader suite, so it
waits for compute mode or the daily tier rather than the lane or the batch
verifier.

### F2. Missing `recovered(cx)` (low, high confidence)

`crates/elab/src/matching.rs:1330`. `undo::recoverable`'s doc says "a
caller that goes on from it calls [`recovered`]", and every other caller
does (`matching.rs:1173`, `matching/as_written.rs:191,224,309`,
`rewrite.rs:965`). Without it, the definition noted as too large stays in the
budget. Today it is harmless in practice: every size error path sets the note
again before it is reported (`value.rs:2962`, `unify.rs:2419`). Still, the
contract is broken, and a future reporting path could then name the wrong
definition. Add `crate::undo::recovered(cx);` in that arm. Size S.

### F3. The fallback note mixes forms (low, high confidence)

`crates/elab/src/matching.rs:1614-1617`. The label now always prints
`s.term`, the expression as written, but the goal falls back to
`goal_normal` when `goal_folded` is `None`. That happens when another
scrutinee was copied into a hypothesis the goal mentions, or when the folded
read-back was too large. The note then reads, for example, "looked for
`isBig 20`", "in the goal `1 = 1`". The "computed" note almost never fires
here, because an unfolded goal rarely contains the written text, so the user
no longer sees `True`, which the old label showed. Either keep the old label
(`normal.unwrap_or(s.term)`) when `goal_folded` is `None`, or always add the
computed note in that case. Size S.

### F4. The "computed" note uses a substring test (low, high confidence)

`crates/elab/src/matching.rs:1632-1634`. `goal_shown.contains(shown)`
matches `f x` inside `f xs` and `1` inside `10`, so the note fires where it
explains nothing. The opposite case is worse: where the expression computes
to something different but the written goal doesn't contain the written
expression, the computed forms that say why are left out. The note's claim,
"which doesn't contain it", is always true, because the warning fires only
when `found(goal_normal)` is false. So nothing it says is wrong, but it can
confuse: where the printed goal visibly contains the printed computed
expression (implicit arguments, eta, shadowed binder names) it reads as a
contradiction. Suggest deciding by term, `occurs(&s.term, goal_folded)`
(both in the `base` context), and also adding the note whenever the printed
computed expression differs from the written one. Size S.

### F5. The goal is read back folded twice (low, high confidence)

`unrefined_goal` (`matching.rs:1329`) and `as_written::search`
(`matching/as_written.rs:283`) both call `cx.quote_folded(goal)` on the same
value in the same context. Each read-back is step-counted, so this is
deterministic, but it is extra work for every generalised `match` that
refines nothing, charged to the declaration's work budget (see F1 on
declarations near their limit). Compute it once and hand it to `search`
through `Today` (it is already a field there). Size S. No perf-log entry is
needed unless someone measures it.

### F6. Test gap at the boundary (low, medium confidence)

The new reject example and the updated `goals/match-call-field-folded`
snapshot show the folded goal. Nothing pins the other side: a `match` whose
scrutinee is found in a hypothesis (so that hypothesis is copied), with a
goal that mentions that hypothesis, must keep today's motive. If that
condition were dropped, the arms would refer to the original hypothesis
rather than its refined copy. The motive would still be well typed, but
proofs that need the refined copy would fail. Add a small `goals/` or
`accept/` example. Size S.

### F7. A scrutinee variable erased by unfolding stays visible (low, low confidence)

When a scrutinee is a variable `x` that the folded goal mentions but
unfolding drops (`P (const 0 x)` with `const a b := a`), the occurrence test
finds nothing and the arms get the folded goal, which mentions the original
`x`. `bind_generalised` has rebound the name `x` to the scrutinee's new
variable (`matching.rs:1352-1354`), so the goal now refers to a hidden,
shadowed `x`. This is sound, since it is the same variable it was before, but
an arm's goal may print it confusingly (`x✝`, or `x` while `x` now means
`Succ k`). This is rare. Worth a look if it shows up in a goals snapshot;
otherwise leave it.

## Checked and sound

- **Equivalence of the motives.** With no scrutinee occurring and no copies,
  `Generalise::apply` (`matching.rs:2058`) replaces nothing and maps each
  level `l < base` to `Var(depth - 1 - l)`. That is
  `goal_term.shift(depth - base, 0)`, which is what the new arm does to the
  folded term (`matching.rs:1409`). Both terms are read-backs of `goal`, and
  `quote_folded` is documented, and built, to give a term convertible with
  `quote`. So the arms' goal is definitionally the old one, and the kernel
  checks the same proofs up to step counts.
- **Contexts agree.** `quote_folded` reads back at `cx.level()`, while
  `quote` uses `base`. All three ways into `generalised_now` set
  `base = cx.level()` and bind nothing before it (`matching.rs:339`, `671`,
  `856`). `as_written::search` makes the same assumption.
- **Refinement decision unchanged.** `any_occurs` and `Generalise`'s hook
  both use `same_shifted` under binders, so "occurs" means the same as
  "would be replaced". A `None` normal form (too large, or `cannot_occur`)
  was "replace nothing" before as well. A scrutinee that occurs only after
  unfolding is caught, since the test runs on the unfolded form. A copied
  variable hidden in either form is caught, since both forms are checked.
  A let-bound variable is read back as its value in both forms, so a copy
  can't hide behind it.
- **Precedence.** As written, when it is found and checks, still wins. When it
  doesn't, the fallback's motive is the folded goal, and for a `match`
  `check_motive` still runs on it (`matching.rs:1086-1088`). `cases` leaves
  its motive to the kernel, as before.
- **Resource fallback.** Only `recoverable` errors, size limits with the
  budget not exhausted, fall back, and they fall back to exactly the old
  path. Steps and size are counted, not timed. The deadline is wall time,
  but it is sticky and never recoverable, so it fails the declaration the
  same way it would anywhere else. Checking doesn't depend on timing
  beyond what it already did.
- **Native pins.** None of the 83 content hashes in `crates/rt/src/natives.rs`
  and `crates/core/src/pins.rs` is among the 950 lines the prelude snapshot
  removes, so no native silently stops binding.
- **Programs as well as proofs.** The path isn't limited to propositions, and
  std programs (`Std.Graph.breadthFirst`, …) change hash through their
  helpers' types. Types are erased, so code generation is unaffected.
- **Comments.** `unrefined_goal`'s and `not_found`'s docs say why, not what,
  and follow CLAUDE.md's rules. The proposal and guide updates are accurate.
- **The 1 Nov codebase review** has no findings in `matching.rs`'s scope.

## Tickets to file

- **SW-2554 follow-ups** (Sonnet, about 45 min): F2, F3, F4, F5 and F6
  together, all in `matching.rs` plus one example.
- **AoC and roguelike check of this merge** (no lane: a compute-mode run or
  the daily tier, F1). Any day that breaks gets a ticket with its proof and
  the arm's goal, for the AoC follow-up model.

## Calls I made

- I rated F1 medium rather than blocking. Elaboration that breaks fails
  loudly and can't produce a term the kernel rejects. std passes. D2441
  accepts regressions found after merging.

## Verdict

**Merge with follow-ups.** The change is sound: arm goals are convertible
with the old ones, and the conditions miss no refinement. Do the follow-ups
(F2-F6) in one small lane, and check AoC and the roguelike against it (F1)
before pushing.
