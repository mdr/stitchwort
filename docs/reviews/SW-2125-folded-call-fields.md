# SW-2125: review of merge `f178669c7` (SW-2096, fields of folded calls)

A fresh-eyes review of stage 2 of `docs/proposals/match-call-field.md`, by
reading only (no builds or runs). Read: `git diff f178669c7^1 f178669c7`,
`machine.rs`, the evaluator paths in `value.rs` that the merge touches or
relies on (`resume`'s projection, `J`, `Unfolding`, `FieldOf` and
`CallField` frames, `branch`, `walk_tree`, `eta_fields`, `unfold_for`,
`unfold_field_for`, `unfold_folded`, `is_folded`, `folded_call`,
`force_call`, `same_spines`), `reference.rs` (`project`, `unfold_folded`,
`eval_tree`), the unifier's folded-call comparison (`unify.rs` 1335-1360,
`spine_pairs`), every `in_kernel_modes` caller and every place that turns
gluing on, the new tests, the SW-2108 review, and SW-2096's ticket notes.

## Summary

The merge is sound and does what it says. The kernel's admission paths
all run inside `in_kernel_modes`, which now sets `Machine::kernel`. Nothing
evaluates for admission outside it. The places that glue outside it (the
inert validator, `inert::candidates`, the elaborator) are either not
admission or only compute sorts. More to the point, the flag doesn't carry
trust. Naming a field `(f x).i` changes no equality: conversion and the
unifier open it through `unfold_folded`, and spine comparison checks the
projections. So a flag left wrong would change only how values and hashes
look, not what's accepted. The elaborator and kernel can't disagree
because of it. The elaborator reads back `Proj(i, f x)`, and the kernel
evaluates that again in its own mode and checks motives by conversion.
Declining SW-2108's F3 was right: `reference.rs` and unglued `value.rs`
both take a field of a lift-leaf call through the lift. The
`reachableIff` hash change is explained (below). The main weakness is that
the "stuck" test that gates naming treats a *folded call* as stuck. It
isn't, and the comments say it is. That's pre-existing in shape (the old
`ProjReady` gave `(g y).i` for the same value), so it isn't a regression.
But it points at a possible glued/unglued gap for `case` on such a field,
which no test probes.

Top recommendations:

1. Probe and, if needed, fix a field of a folded call whose unfolding ends in
   another folded call (F1): the "stuck" test accepts it, and a `case` on
   such a call field may stay stuck glued where unglued computes.
2. Add a kernel-glued mode (`glue` and `kernel` both on) to
   `proof_equivalence`'s matrix, and a test that admission actually runs
   with `kernel` set (F2).
3. Put `in_kernel_modes`'s four restores in one guard, or keep the
   documented policy that a panicked session is dropped (F3; the 1 Nov
   review's 4.1).
4. Make a scrutinee reached through a solved metavariable, and `ReplayElim`'s
   projection, name a folded call's field the same way, or note the
   difference in §10 (F4).
5. Make the kernel half of `a_folded_calls_field_stays_the_calls_in_the_elaborator_only`
   able to fail, and check `callFound`'s claim (F5).

Findings: high 0, medium 0, low-medium 1 (F1), low 5 (F2-F6).

## Findings

| # | Where | What | Severity | Confidence | Fix |
|---|---|---|---|---|---|
| F1 | `value.rs:1681-1687` (`FoldedField`), `value.rs:2122-2132` (`eta_fields`) | "Stuck and not a metavariable" also accepts a folded call, which isn't stuck. The doc's invariant is overstated, and a possible glued/unglued gap for `case` on such a call field is untested | low-medium | medium | M (probe first) |
| F2 | `proof_equivalence.rs:220-232`, `call_fields.rs:161-170` | No matrix row for the kernel's own glued mode. Nothing checks that admission runs with `kernel` set | low | high | S |
| F3 | `machine.rs:72-88` | The `kernel` flag is restored by hand, like the other three modes. A panic leaves it set | low | high | S |
| F4 | `value.rs:2123-2131`, `value.rs:1859` | A folded call reached through a solved metavariable still shows its unfolding's internals in its fields | low | medium | S-M |
| F5 | `call_fields.rs:172-174, 201-206`; `examples/accept/match-call-field-folded.sw:19-21` | The kernel half of the elaborator/kernel test passes vacuously if `Term`'s `Debug` changes. `callFound` may not test what its comment says | low | medium | S |
| F6 | `value.rs:1674-1687`, `2319-2351` | Applying or `J` on a field of a chain of `d` folded calls runs O(d²) trees. One `Box` per glued projection of a folded call | low | medium | none now |

## Details

### F1. A folded call counts as "stuck"

`Frame::FoldedField` names the field `(f x).i` when the value `f x` unfolded
to is `Neutral(head, _)` with a head that isn't a metavariable.
`eta_fields`'s new branch uses the same test on `forced`. The comments
justify it with "then every field is stuck either way, so this names it
without changing what it computes to". But a folded call
(`Neutral(Def g, args)` with `folds(g)`, a `decreasing` definition, a
dictionary or a theorem) passes the test, and it isn't stuck: it's only
not unfolded yet.

**Reaching it.** `f`'s case tree reaches a leaf that is a call of a
non-folded definition, kept as a glued `Value::Call` while gluing (a
`decreasing` definition's fuelled helper). `Frame::Unfolding` doesn't
recognise that as a folded call. It pushes `next` and forces it.
`force_call` runs the helper's tree. If the helper's leaf is a call of
another folded definition `g y`, the forced result is `Neutral(Def g, [y])`.
`Frame::Unfolded` doesn't force it further (`needs_forcing` is false), and
it reaches `FoldedField` or `ScrutineeReady`/`branch` as it is. Examples:

- A `decreasing` definition with a tail call to another `decreasing`
  definition.
- A theorem whose proof is another theorem's call. That is
  `reachableIff`'s case (below).

**What it does now.** The field is named `(f x).i`. Before the merge,
`ProjReady` gave `project(g y)`, the call field `(g y).i`. Both are lazily
computed names that conversion, application and `J` open (`is_folded`), so
what's equal by `conv` hasn't changed, and the merge didn't regress this.

**Why it matters anyway.**

- The stated invariant is wrong, and the next change built on it may rely
  on it.
- A `case` on a call field whose type isn't a record goes
  `Scrutinee` → `folded_call` false (the spine is longer than the arity) →
  `branch` → `stuck_tree`. Unglued, the same scrutinee computes: the
  `Unfolding` frame keeps unfolding folded results. If that happens, glued
  evaluation leaves a stuck `case` where unglued and the reference give a
  constructor. That breaks D3030 in the incomplete direction: the
  elaborator, and the kernel's glued body check too, would reject an
  equality unglued evaluation accepts.

I couldn't run anything to confirm the second point. The matrix has no
term of this shape: `countDown` recurses through its own helper and never
reaches another folded call.

**Change.**

1. Add matrix terms to `fields_of_calls_are_compared_alike`: a `decreasing`
   `outer x` whose leaf is `inner x`, another `decreasing` definition
   returning a record with a `Nat` field, and a definition that `match`es
   on `(outer n).count`. Then see whether glued and unglued disagree.
2. Either way, tighten the test in `FoldedField` and `eta_fields` to
   `Neutral(..)` that is neither a metavariable nor `folded_call`. For a
   folded call, continue as `ProjForced` would: push the frame again and
   unfold. Or, if the probe shows it's equal anyway, correct the two
   comments to say "stuck, or folded".

If the probe shows a disagreement, the same fix likely belongs in
`ProjReady` and `ScrutineeReady` (pre-existing). Size M, Opus (core
evaluator).

### F2. The kernel's own mode isn't in the matrix

`proof_equivalence`'s `How` has `glue`, `shortcuts` and `reference`.
`matrix` never sets `kernel`, so `GLUED` is the elaborator's mode. Before
stage 2, that was also how the kernel checked a body. Now the kernel's
glued mode (`glue` and `kernel` on) is a fourth mode that only
`call_fields::a_folded_calls_field_stays_the_calls_in_the_elaborator_only`
touches, for one term, by setting the flag by hand. Nothing checks that
`admit_group` and `declare_def` actually run with `kernel` set. If someone
later calls the checker for admission outside `in_kernel_modes`, nothing
would notice. That would be harmless for soundness (see the summary), but
the hashes would change silently.

**Change.** Add `kernel: bool` to `How`, set it in `matrix`, and add the row
`How { kernel: true, ..GLUED }`. Add a core unit test that
`in_kernel_modes` sets `kernel` and restores it, nested too. Size S,
Sonnet.

### F3. Manual restore

`in_kernel_modes` restores `glue`, `kernel`, `transparent` and `erasure` by
hand, so a panic in `f` leaves `kernel` set. I checked every
`catch_unwind`. `host/stack.rs` raises the panic again in the caller.
`standalone/lib.rs` turns it into the exit status. The fuzz tests check one
text per session. No host reuses a session after a panic, so this is the
1 Nov review's 4.1 extended by one field, not a live bug. If it stayed set,
the elaborator would show unfolded internals again. That changes display
and hashes, not trust.

**Change.** Fold the four restores into one guard, or keep the comment's
"nothing needs a guard" and add the review's suggested policy line
("a panicked session is dropped") to `Machine`'s doc. Size S, with F2.

### F4. A solved metavariable shows the internals

`eta_fields`'s folded branch needs `folded_call(g, unforced)`. If the
scrutinee is a solved metavariable whose solution is a folded call,
`unforced` is the metavariable, and the fields are projections of the
unfolding. The same goes for `Frame::ReplayElim` (`value.rs:1859`), which
replays a solution's projection by `unfold_folded` and then `project`. So
`(f x).i` reached that way shows the fuelled helper, and a `match` inside
it rewrites inside the call again: the same symptom as §2.2, in a rarer
spot. This affects display only. Glued calls behave the same way through a
solved metavariable (the `Value::Call` branch keys on `unforced` too), so
this is consistent with existing practice.

**Change.** Force `unforced` through solved metavariables only
(`force_solved`) before the `folded_call` test, and name the field in
`ReplayElim` the same way, or record this as a known gap in §10. Size S-M,
with F1.

### F5. Tests that may not fail

- `mentions` looks for `Def(DefId(N))` in `{term:?}`. The elaborator half
  of the test also checks the term's structure, but the kernel half is only
  `!mentions(..)`, which passes if `Term`'s `Debug` output changes. Walk
  the term instead.
- `callFound`'s comment says "a `match` on the call finds it there". The
  `match same: pick n empty with | result => rewrite h in rfl` arm only
  works if the goal still holds `pick n empty` for `h` to rewrite. That
  happens if the variable pattern doesn't abstract the call, in which case
  the example doesn't show the match finding the call (confidence low, I
  couldn't run it). `armsKeepCall` and the goals snapshot do test the
  claimed behaviour. Either drop `callFound` or make it bind and use
  `same`.

Size S, with F2.

### F6. Cost

- Applying (or `J` on) `(f x).i` where `f x` unfolds through a chain of `d`
  folded calls: `FoldedField` unfolds to the end of the chain, and the
  result is named one level down. Then `computes_field` reruns that
  level's tree through `unfold_field_for`, and so on. That's O(d²) tree
  runs, not O(d). It's not exponential, because there's no doubling.
- Each glued projection of a folded call allocates a `Box` and clones the
  call value.

Day 23's audit got faster (12.2 s to 9.5 s), so neither shows today. No
change now. Revisit if a profile shows `unfold_field_for` under
`FoldedField`.

## Answers to the brief's questions

1. **Is the kernel unaffected?** Yes.
   - Every admission function (`define_def`, `define_group`, `declare_def`,
     `retype_def`, the `admit_trusted_*` replays, the data
     declarations, validators, pins, natives) is entered through
     `in_kernel_modes`.
   - Glued evaluation outside it: `reference::not_a_proof` and
     `inert::candidates` compute only sorts. `elab` uses `kernel::infer`
     under `without_glue`, so it doesn't name. Programs run unglued.
   - Nesting: the elaborator calling admission mid-elaboration saves and
     restores `false`. Nested `in_kernel_modes` restores `true`. Errors
     return through the closure, so an early return can't skip the
     restore. Only a panic can (F3).
   - `EvalCaches` holds only hashes and erasure, so no value crosses
     between modes.
2. **Can elaborator and kernel disagree?** Not through this change.
   - The stuck form reads back as `Proj(i, f x)`, which the kernel
     evaluates again in its own mode.
   - A `rewrite` or `match` motive abstracts `(f x).i` or `f x` in the
     read-back term. The kernel checks it by conversion, which is
     semantic.
   - Conversion and the unifier open the name (`unfold_folded`).
     `same_spines` and `spine_pairs` compare projections, so
     `(f x).a ≡ (f x).b` can't slip through. The only new freedom is the
     existing folded-call policy: `same_arguments` solves metavariables
     from the call's arguments. That now applies to the fields as well,
     which can choose a different (well-typed) solution than unfolding
     would.
3. **The stuck test.**
   - Excluding `Head::Meta` is right: an unsolved metavariable's field must
     stay something the unifier can solve.
   - It can't hide a solution. A name over arguments that hold a
     metavariable is opened by `unfold_folded`, which forces the arguments
     afresh.
   - No loop: `unfold_folded` projects directly, not through
     `FoldedField`. `FieldOf` descends one definition per step, its
     own-tree check is by `ptr_eq` on the call's spine, and the budget
     bounds the rest.
   - But "stuck" includes folded calls (F1).
4. **Declining F3.** Right.
   - `reference.rs:111` `project` calls `unfold_folded`, which runs
     `eval_tree` with `fold_lifts = false`: through the lift.
   - Unglued `value.rs` reaches `Frame::ProjForced` with `folded_call` true
     (`folds_on_lift`), and `unfold_for` passes `false`: through the lift.
   - So all three compute through it, and SW-2108's premise ("stays folded
     unglued and in the reference") was wrong. Its flag would have left
     glued `(f x).i a` rigid.
5. **Do the tests prove their claims?** Mostly.
   - The value-level tests cover stage 1's `App` and `J`, opaque calls,
     the lift leaf and stage 2's projection.
   - Rule 2 (`eta_fields`) is covered only through the examples and the
     goals snapshot, which is adequate.
   - Gaps: F1's shape, the kernel's glued mode (F2), and a metavariable
     scrutinee (F4). F5 lists the weak assertions.
6. **`reachableIff`.** Explained, and an improvement.
   - `let (Both found complete) := Graph.distancesShortest graph starts`
     is rule 2 on a theorem's call (theorems fold).
   - That proof is `Graph.shortestOfResult …`, another theorem's call,
     whose unfolding is stuck outside its own tree.
   - The fields used to be projections of `shortestOfResult`'s internals.
     Now they're `(distancesShortest graph starts).left`/`.right`, so the
     elaborated term and its `%match` helpers changed.
   - No other std hash moved. Per SW-2096's notes, the whole AoC ran with
     0 errors and the roguelike was clean on main. I didn't rerun either.

## Checked and sound

- All admission entry points are inside `in_kernel_modes`. Nothing in
  `EvalCaches` carries values between modes.
- `Frame::FieldOf`'s `J` branch now pushes `JProof`, which forces first,
  so a `Value::Call` field no longer reaches `JForced`'s panic (SW-2108 F2).
- `FoldedField`'s `project(d, i, value.clone())` names the call *before*
  unfolding. If the call is stuck in its own tree, the `Unfolding` frame
  hands back the call itself, and the name equals the projection.
- `ProjForced`'s `is_eta_type` gate and `eta_fields`'s reach only through
  `eta_case`: both only for record types.
- `walk_tree` (the stuck-tree comparison) excludes folded scrutinees before
  `eta_fields`, so the new branch doesn't fire there.
- Day 23 is back on its original proof without `largestFromAnswersAt`, and
  no statement changed.
- The §10 text in the proposal matches the code.

## 1 Nov review (rust-codebase-review.md), findings in scope

- **4.1, manual restoration:** still open. This merge adds one more
  manually restored mode (F3).
- **1.5, the kernel boundary:** unchanged. `Machine::kernel` is a `pub`
  `Cell`, like `glue`, but it carries no trust (summary).
- **4.4, large files:** `value.rs` was 3,790 lines and is now 4,781 lines.
  The frame machine's field-of-call handling (`CallField`, `FieldOf`,
  `FoldedField`, `computes_field`, `unfold_field_for`) is now a separate
  concern spread through `resume`. It's a candidate for its own module
  when someone next touches it, but not worth a lane alone.

## Tickets to file

- **Lane A (Opus, 60-75 min): folded calls counted as stuck.** F1's probe
  (matrix terms for a `decreasing` tail call to another folded definition,
  and a `case` on its `Nat` field), and the fix in `FoldedField` and
  `eta_fields`, plus `ProjReady` and `ScrutineeReady` if the probe shows a
  disagreement. F4's solved-metavariable consistency. Targeted tests:
  `proof_equivalence`, `call_fields`, and the
  `match-call-field-folded` examples.
- **Lane B (Sonnet, 30-45 min): stage 2 test and guard hygiene.** F2's
  kernel-glued matrix row and the `in_kernel_modes` flag test. F3's guard
  or policy line. F5's term walk and `callFound`.

## Questions for Matt

None.

## Calls I made

- The doc's name follows the lane brief (`SW-2125-folded-call-fields.md`),
  not the generic `code-review-<NAME>.md`.
- I didn't move the ticket: the review rules say not to edit
  `board/tickets.json`. The orchestrator moves it.
- F1 is rated low-medium, not medium. It can only make glued evaluation
  decide fewer equalities, never more, and its shape predates the merge.
