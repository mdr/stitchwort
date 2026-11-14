# SW-2876 review: `f.induct` strips decrease-proof marks from hypotheses and splits

Paper review (D2364: code that generates kernel terms) of `lane/SW-2876`,
commit `4a57a1811`. Nothing was built or run. Line numbers are in
`crates/elab/src/equations/induct.rs` on the lane unless stated otherwise.

**Verdict: OK to merge. No must-fixes.** Every term the change touches
goes to the kernel, which checks `f.induct`'s statement and proof. So a
wrong strip, or a mark that's missed, can only make the kernel refuse the
proof. That is recorded as an `E-NO-EQUATION` skip and is never unsound.
The risks are lost theorems, not false ones.

## (1) Where a marked call can still get through: OK

Marks come only from `rec_term` (`equations.rs:5552`), for `%rec` in a
`decreasing` tree. In `f.induct`, they reach these places:

| Where | Status |
|---|---|
| Right side `Case.rhs` | already unmarked (`induct.rs:503`) |
| IH arguments and IH decrease proofs (`calls`, 262/265) | already unmarked, including calls nested in a call's arguments |
| Case binders: variables, overlap and guard hypotheses, split hypotheses | **new**, 563–565: all of them, including `binders[..tk]`, which become `RowProof.binders` and the tree walker's `at_leaf` types (2695) |
| Split terms: `Step::Ite/Dec/Helper` `args` | **new**, `unmark_step` 321–375. These are the only step fields the proof reads (`args[1]`, `args[0]`/`args[2]`, `args[col]` in `induct_split`, 987–1060) |
| Motive, conclusion, case left sides | never contain calls of `f` |
| Tree walker's guard arguments | `PV::Rec => None` (2424), so a guard that calls `f` is skipped, not marked |
| SW-2868's nested splits and catch-alls (on main) | they build their `J` terms only from `scrut` (`args[col]`) and `case.binders[..]` types (merged file 1097, 1545–1725, 2094–2145), and both are now unmarked when the case is built. Nothing downstream reads a raw tree term. |

Fields that are left marked: `Step::Helper.proof` and `.result`, and
`Step::Dec.uniq`. These are inert: when `marked` is set, `proof` is `Refl`
and `uniq` is `None` (`equations.rs:3701`, 4091), and `induct.rs` never
reads `proof`, `result`, `uniq`, `normal` or `col_tys`.
**NOTE:** `unmark_step` strips `normal` and `col_tys` but not
`proof`/`result`, and nothing reads any of them. Either strip only `args`
(simplest, and true to the doc comment "the terms the proof takes from
it"), or strip every term field. That's a matter of taste, so it can wait.

## (2) Stripping never removes a real argument: OK, with one theoretical case (NOTE)

`unmark` (`equations.rs:5611`) drops the last argument only from a spine
whose head is `Def(f)`, that has exactly `n + 1` arguments, and whose
outermost application is `Icit::Auto`. `spine()` strips `Loc` at every
level (`core/src/term.rs:435`), so a `Loc` can't hide a mark.

- **More arguments:** `f y… p z` has `n + 2` arguments, so the outer
  application isn't stripped. Recursing into the head strips `f y… p` to
  `f y…`, which is correct.
- **Partial application:** fewer than `n + 1` arguments, so nothing is
  stripped. A `%rec` lambda that is never applied keeps `f y… Var0` inside
  its body, and that call is stripped. This is correct, because the
  lambda's `decreasing` binder becomes unused and no index shifts.
- **Under binders:** deleting an argument changes no de Bruijn index, so
  no shift is needed.
- **The theoretical miss:** if `f`'s result type is a function whose first
  binder is `Auto`, then a full over-application `f y… inst` looks exactly
  like a mark and is stripped wrongly. Before this change only the right
  side ran that risk; now hypotheses and split terms do too. The kernel
  would refuse the result, so it is a lost theorem, not an unsound one.
  `unmark` also runs for structural definitions, since `mark_rec` is set
  for every kind, even though only `decreasing` makes marks.
  **NOTE:** a cheap tightening is to return early from `unmark` unless
  `d.kind` is `Decreasing`. That removes the false match for structural
  definitions entirely.

## (3) The IH decrease proofs are still correct: OK

This commit doesn't change `Ih.proof` (`calls`, 265: the call's own `p`,
lowered and unmarked). The proof `p` may refer to a hypothesis binder
whose type the commit now unmarks (`h: f rest = None`). The new type is
the one the kernel can actually check, and it is the type of the
equation's matching parameter, which was made without marks. So `eqn`
applied to the binders (1247–1250) now agrees with the case's binder
types. Before this change it couldn't have type-checked whenever a binder
held a mark. The `%rec` application in `induct_leaf` (1290) is unchanged.

## (4) Composition with SW-2868 on main: OK, clean merge

`git merge-tree --write-tree main lane/SW-2876` gives a clean tree
(`b4a29985b`). The lane's two hunks (the new `unmark_step` after `calls`,
and the unmarking in `induct_cases`) don't overlap any of SW-2868's hunks,
which start at line 42 and at line 981 onwards. The fix is applied when
each `Case` is built, before any split is generated, so SW-2868's nested
and catch-all code only ever sees unmarked binders and scrutinees (see
the table in (1)). The commit message's claim that `readPackets.induct`
now stops at the nested `Some (False, …)` was made before SW-2868 landed.
After the merge it may get further or stop somewhere else. The verifier
should look at the reason it gives, not at the lane's message.

## (5) The suggested `debug_assert` guard: worth adding, but not as worded (SHOULD-FIX, can be a follow-up)

The guard as worded, "no `Def(f)` with more than `f`'s parameter count of
arguments", would fire on legitimate over-applications such as
`f y… z` when `f` returns a function. A precise version reuses
`unmark`'s own predicate: `debug_assert!(unmark(g, d, &t)? == t)` (or a
`has_mark` walker that shares its match arm), run on `ty` before
`declare_def` and on the finished proof term. Restrict it to
`Decreasing`, as in (2).

Is it worth having? Today a missed mark doesn't show up anywhere unless
someone names `f.induct`: the kernel refuses the proof and it's recorded
as a skip (that is how 2021 day 16 found this bug). An assertion would
turn the next missed mark into a test failure on any example that has a
`decreasing` definition. It costs one tree walk in debug builds. I
recommend adding it, as a small Sonnet follow-up.

The structural alternative is to make the mark a wrapper that the kernel
can't mistake for an application, so that a leak fails at once
everywhere. That is a bigger change and isn't needed now.

## (6) The example says what it claims: OK, with a NOTE

`examples/accept/function-induct-call-in-scrutinee.sw`: `settle` calls
itself in a `match`'s scrutinee and again in the `Some` alternative.
`settleNone` uses `settle.induct` with a `none` case that has no IH and a
`some` case with one IH (`ih`), which closes the goal `settle rest = None`
directly. So the case shapes match the header comment ("only the
alternative's call gets an induction hypothesis"). Before the fix,
`settle.induct` isn't made and the theorem doesn't elaborate, so the
example does guard the bug. The hash snapshot pins `Main.settle.induct`'s
exact statement, including the hypothesis `settle rest = None`.
**NOTE:** the proof never uses the type of the `none`/`some` hypotheses,
so the `.sw` file on its own doesn't show the "as the equations state it"
part. Ascribing the binder in a case lambda (for example
`(none: settle rest = None)`), if the syntax allows it, would make the
example show that by itself.

## Summary

| Check | Verdict |
|---|---|
| (1) every place a mark can get through is stripped | OK. NOTE: `unmark_step` strips unread fields inconsistently |
| (2) no real argument is stripped | OK. NOTE: a result type that is an `Auto` function is a theoretical false match; restrict `unmark` to `Decreasing` |
| (3) IH decrease proofs | OK |
| (4) composition with SW-2868 | OK: clean merge, and the fix comes before the new code |
| (5) `debug_assert` guard | SHOULD-FIX as a follow-up, using `unmark`'s predicate, not an argument count |
| (6) example | OK. NOTE: ascribing the hypothesis would make the example show its claim |
