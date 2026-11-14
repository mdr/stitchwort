# SW-3281 review: comparing a call's written result by arguments in `propagation_plan`

Reviewer: Opus, 14 Nov 2026. Branch `lane/SW-3281` (3bbaaba00), against
`main` at 1aeae23d4. Probes ran on the branch's release binary and on the
main checkout's release binary (built 23:36 from `main`, whose `check.rs`
matches the merge base); the probe files are in the review's scratch folder
(`p*.sw`, `q*.sw`, `d*.sw`, `e*.sw`, `s*.sw`, `gen2.py`).

## The change

`propagation_plan` compares a call's result type, as written, with the type
expected of it before the arguments are checked. It used plain unification,
and fell back to `unify_solving_arguments` only when some argument was
written `_`. Now it always falls back. For `Parse.readsThen` against
`Parse.Reads twoLetters Written`, plain unification fails (the unfolding is
stuck on `?p ()`), so before the change the call was inferred without its
goal: `t` stayed unknown, the lambdas were checked in place, failed, and were
checked again after the expected type. With the change, the comparison by
arguments solves `?p`, `?j` and `t` first.

## Verdict

The success path is sound and the gain is real: an elaborated term is still
checked against its expected type, and the kernel checks everything, so a
guessed solution can't make a wrong proof go through. I found no program the
old checker accepted that the new one rejects. Two kinds of probe (a wrong
guess on an outer unknown, and a proof split differently from its parser's
`let`s, `p2`–`p8`, `s1`, `s2`) behave the same on both binaries; in several
of them the old ordinary path already makes the same argument-wise guess.
The failure path is a regression, though. When the propagated attempt fails,
`propagate_failed` re-elaborates the call with `infer` (no expected type) and
`no_propagation` raised for everything inside it. That isn't the path the
call took before the change (`fallback_inferred`: `infer_expecting`, nested
propagation on). On a `readsThen` chain that re-elaboration can't check even
the first, correct, argument, so **any error anywhere in a `readsThen` proof
is now reported as a large type mismatch at the outermost first lemma**,
instead of at the real fault. One must-fix.

## Must-fix

**M1. Errors inside a `readsThen` chain move to the outermost first argument.**

Probe `d8bad.sw`: eight nested `Parse.readsThen Parse.readsNat (r x h => …)`
ending in `Parse.readsDone [x0, …, xBad] _ rfl`, with `xBad` not in scope.

- main: `E-UNKNOWN-NAME` at `xBad` (line 25).
- branch: `E-TYPE-MISMATCH` at the first `Parse.readsNat` (line 17):
  "expected `∀ (state: Parse.State) … Parse.runFrom state (arg =>
  Std.Effect.bind … …) = Ok (value, after) → …`, but this has type
  `Parse.Reads Parse.nat (…)`". Its notes say `?2` (`p`) wasn't worked out,
  and add a long note about `Parse.nat`'s inner `match`. Nothing in it
  points at the real error.

The same happens at three levels (`d3bad`), at fourteen (`d14bad`, no
blow-up: 0.47 s against 0.73 s), and in the lane's own miniatures with the
pair swapped (`e1.sw` over characters, `e2.sw` generic). In those, main
blames the inner `rfl` and the branch blames the outer `Prs.readsSatisfy`.
Correct proofs still check (`d3ok`, `d8ok`, `s1`, `s2`). Parser proofs are
the main users of this path, and stage 1 sweeps them, so everyone writing
one would see this message for every slip.

Why: the plan used to return `None` when plain unification failed, and the
call went through `fallback_inferred`. There, `finish_application`'s
after-expected comparison (also by arguments) solves `?p` before the held
first argument is checked again. The re-elaboration in `propagate_failed`
uses bare `infer`, so `readsNat`'s type meets `Reads ?p ?first` with `?p`
applied to `()`, which plain unification can't solve. That error is outside
the propagated error's argument, so `in_same_argument` keeps it. The
`no_propagation` raise also turns off plain propagation, by-holes
propagation and `propagate_comp` for the whole subtree. By-holes plans
already pay for this, but there the user wrote the `_`s.

Suggested fix (untested): when the plan matched only by arguments (plain
unification failed), on failure restore the snapshot and finish exactly as
the pre-change `None` path did. That means `fallback_inferred(cx, expr,
expected, named)`, with a counter that turns off only the argument-wise
fallback in nested plans, so a failing chain isn't tried twice at every
level. Plain and by-holes propagation stay on inside. Then failing programs
get exactly the old messages, and anything the old checker accepted is still
accepted by construction. Add a reject example (an unknown name in the last
step of a three-step `readsThen` chain with no `_`s, `expect-error:
E-UNKNOWN-NAME`) so this stays put. No existing example covers it:
`reads-nested-binds-unknown-field.sw` uses `readsBind _ _ _ _`, so it takes
the by-holes path, which is unchanged.

## Should-fix (ticket)

**S1. The argument-wise guess runs on every call whose plain comparison
fails, before `compare`'s other routes.** Those routes are instance search
(`unifies_with_instances`), effect coercion, row postponement, waiting
helpers and `compare_waiting`. Before the change they ran first for these
calls. Now a lossy solution from comparing arguments is committed first, and
the routes only see what's left. My probes found no case where this changes
the outcome. A dictionary unknown solved from the goal's own call
(`q2.sw`, `sum-dictionary-from-expected-type.sw`) behaves the same, and so
do a dozen accept examples on instances, decisions and binds that I spot-ran.
Still, it changes the order of rules the postponement design depends on.
The cost on error paths and on non-parser code is unmeasured: the lane
measured Std.Parse (−18%) and 2020 day 2 (−21%). Worth a ticket: compare
whole-AoC and std step totals before and after on Overmind, and if a
non-parser regression shows, limit the fallback to results whose head is a
`Prop`-valued definition (the lemma conclusions it was meant for).

**S2. Pre-existing, found on the way:** `theorem sumCong [a: Type] [add: Add
a] (xs: List a) …: xs.sumBy f = xs.sumBy g` used against an `Int` goal fails
on both binaries with `?1 xs` (`add`) unsolved (`q2.sw`, `useI`/`useI2`).
The goal names `Std.Int.instAdd` in that very position. It may be expected,
since `add` is an implicit, not an instance argument. If it isn't, it's a
small ticket.

## Nits

**N1.** The new comment in `propagation_plan` ends with "(SW-3281: a
two-step `readsThen` chain took 498k steps, 61k with this)". That describes
the change and belongs in the commit message (CLAUDE.md, comments rule).
The why before it is good. The test's doc comment gives other figures (349k
to 46k on the miniature), so a reader sees two before-and-after pairs for
"the same" chain.

**N2.** `reads_chain_cost.rs` is sound. Step counts are deterministic, the
two programs run in separate sessions, and 25% over a bound of 38k/32k
catches a return to 349k/208k by a wide margin. Being well under a bound
only prints. It passed (3.5 s). One caveat for whoever updates the bounds:
the count is `with − without` in a rewound session, so caches warmed by the
first load make it a little lower than `STITCHWORT_TIMINGS`. The doc says
so.

## The 38 hash changes

- The 29 named theorems (22 Std.Parse, 7 example theorems): their statements
  come from their written signatures, which elaborate before the body, so
  only the proof terms can change. The lane's type-hash comparison (one hash
  per name before and after, all equal) agrees.
- The `%match` helpers: 9 are in the lane's changed list. The type hash
  changed for 7 (`readsBefore.%match1`, `readsLooseRow.%match1`/`%match3`,
  `readsNatDigits.%match3`, `readsSection.%match1`, `readsSpaces1.%match1`,
  `readsToken.%match1`). For `readsOneOfFrom.%match1` and
  `readsSatisfy.%match1` only the term changed. A helper's type comes from
  the `match`'s context and motive. These matches sit inside lambdas under
  calls such as `Parse.readsWeaken [spec := …] (Parse.readsBind _ _ _ _ …)`,
  whose `?p` is now solved directly from the goal's argument (`() =>
  Parse.satisfy what passes`) instead of later through `readsBind`'s
  conclusion. So the hypotheses in scope at the `match` carry a solution
  that is definitionally equal but written differently. That's harmless:
  source can't name these helpers, and the parent theorems' statements are
  unchanged. I didn't print one before and after (the lane's dump hashes
  `Debug` output and no CLI prints a helper's type), so this is inferred
  from the code, not observed.

## Questions from the brief

1. *Wrong commitments.* Any failure in the call's own application restores
   the snapshot, so a guess that its arguments contradict can't stick. What
   can stick is a guess on an outer unknown that the call's arguments don't
   touch and that only later code contradicts. I built that shape (`p3`,
   `p4`, `p8`); main makes the same guess there today. Held lambdas,
   postponed arguments and proof searches are checked after the plan, under
   the restore. Dot calls go through `prefix_form` as before. Implicit
   instances: S1. Abilities: `propagate_comp` is unchanged (still plain
   only). The real hazard is the fallback, M1, not the guess.
2. *Errors.* Ordinary call type errors are unchanged (`q1.sw`, `q2.sw`,
   `p5.sw`, identical output). Errors in `readsThen` proofs regress (M1).
3. *`%match` helpers.* Harmless (above).
4. *Step test.* Sensible and deterministic (N2).
