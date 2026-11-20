# SW-4370: review of lane/SW-4226 (`cases` splits under an earlier split's equation)

Reviewer: Opus paper lane, 20 Nov 2026. Branch `lane/SW-4226`, one commit
`061e2943d`. Read from the code only; nothing built or run.

**Verdict: merge after two small fixes (docs).** The code is right as it is.

## What changed

`node` (crates/elab/src/cases.rs) gets one more step, after the fallback and
before `open_case`: in the second try (`run.thrifty`) only, `Finder::under_split`
looks through the case's split equations, latest first, skipping stale copies,
and walks each equation's stuck side with the ordinary `Finder::walk`. The
first atom it returns is split with the ordinary `split_on(.., fallback: false)`.
One new accept example, its hash snapshot, and doc paragraphs in
`docs/proving-guide.md` and `docs/syntax.md`.

## 1. "Nothing `cases` proves today changes": true

- First try: the new step is gated on `run.thrifty`, so the first try runs
  the same code as before and gives the same terms.
- Second try: the step sits where `node` used to return the `E-CASES` error
  of an open case. Nothing catches a `node` error and tries something else:
  the four other callers of `node` (`introduce`, the two fact-adding
  `let` builders, `substitute`) propagate with `?`. `split_on` goes through
  `matching::generalised_named`, whose retries (`undo::attempt`, the
  transport retry) wrap only binding the motive, not the arms' bodies. A
  failed arm goes to `branch_errors`, and the attempt ends `Err`. So if the
  new step runs at all, that second try used to fail as a whole. A second
  try that closes today never reaches the new step, and its term is
  unchanged. Any `cases` that closes today closes the same way.
- `under_split` builds a fresh `Finder` and uses only what `walk` returns
  (`best`). It doesn't touch the `single`/`last_resort` of the finder whose
  results `node` already used. Its only side effects are `run.splittable`,
  a cache of a pure function, and step counting.

## 2. Looping and blow-up: bounded

- `walk`/`chain` return `best` only for a type with two or more
  constructors that isn't recursive (`splittable`), and only for a value not
  already known in the case (`!is_known`, which reads the case's split
  equations). Once `tok` is split it is known, so the same equation can't
  hand back `tok` again. A value split already but stuck again goes only to
  `resplit` → `last_resort`, which `under_split` ignores. Records (`single`)
  and recursive types (`resort`) are ignored as well.
- Every `under_split` split adds at least one case (n ≥ 2), so the 256-case
  cap of the second try bounds the depth and width of the splits. Behind
  that are `VISITS` (100,000 per walk) and the 20-million-step `limited`
  budget around the whole attempt, which counts `walk`'s steps.
- If the generalisation can't see the atom in the equation, the equation
  stays stuck on a value that is now known. `walk` then returns nothing,
  the search moves to earlier equations, and the case ends in
  `open_case` as before. There is no loop.
- Equations of fallback splits and number splits (`flag = True`, `n = 32`)
  are stuck on a bare variable. `walk` finds nothing there, which is
  correct.

## 3. Terms: ordinary splits

The split is `split_on` with the same `Atom` shape the goal search
produces. It goes through `generalised_named` with `stale`, and each arm is
an `Expr::Cases` that comes back to `node`. Nothing new is put together by
hand. The kernel checks the resulting `match` like any other split's
(D2364: no new term form, no new trust).

## 4. The error on failure: unchanged

When both tries fail, `cases_goal` reports the first try's error, with the
"second try ... 256 cases" note keyed on the *first* try's `ran_out`. The
second try's own error is dropped. So a `cases` that still fails shows the
same message as before. The one exception is a fatal `E-RESOURCE` in the
second try, which is passed through. The extra splits could in principle
use up the declaration's own resources where the second try used to stop
early. That risk isn't new, since the second try could already make 256
cases. A failing `cases` may now take longer, up to the second try's 20M
steps / 256 cases. I'd accept that; the verifier's reject examples will
show it if it costs anything visible.

The reason given for keeping the step out of the first try is sound. A
first-try failure that used up the step budget would skip the second try
(`e.code == "E-CASES-BUDGET" && !out_of_cases`).

## 5. Docs: two small fixes

1. **proving-guide.md**, the `cases` bullet. The new sentence leaves out
   that this happens only in the second try (so with `arithmetic` before
   each split and the 256-case budget). It also reads as if it applies to
   comparisons only, when it applies to any earlier split's equation that
   is stuck on a finite-type value. Suggested wording: "A comparison of
   numbers is split whole, true or false; when a case is still open after
   that, the second try (below) splits what the comparison's equation
   still waits for: ...". Also rewrap the line ending
   "`(examples/accept/cases-under-comparison.sw`). `cases then t` tries `t`
   in every case", which runs past the paragraph's 76-column wrap.
2. **syntax.md**, the "A second try" bullet. "a case still open after the
   fallback has split what its earlier splits' equations are still stuck
   on" reads as if the fallback did the splitting. Suggested: "And a case
   still open, with no fallback split left, splits a value of a finite
   type that an earlier split's equation is still stuck on: ...". The rest
   is accurate.

## Checks for the orchestrator

- D3608: confirm that `cases-under-comparison.sw` fails on `main`. The lane's
  report should show it, and from the code it must: `levelBelowFive`'s
  `True` case has the goal `True = False`, which mentions no variable for
  the fallback. The verifier's named runs: that example, its
  `hash_stability` snapshot, and the `cases-*` reject examples
  (`cases-step-budget`, `cases-split-too-large`, and the plain `E-CASES`
  ones) to confirm their output is unchanged.
- Not a narrowing (D3688): `cases` accepts strictly more.

## Findings worth a ticket (backlog, small)

- The fallback picks only variables the *goal* mentions. A goal that
  computed to `True = False` mentions none, which is why this second-try
  step was needed. If the fallback also considered variables that the
  case's stuck equations mention, the first try would close these goals
  too, with the 64-case budget. But it would change the terms of proofs
  that only the second try closes today, and a first try that ran out of
  steps would skip the second try (the lane's own reason). Worth an Opus
  look, not urgent.
