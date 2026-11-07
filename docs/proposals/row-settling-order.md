# When a call's effect row may be settled as empty

SW-1926, 7 November 2026. Read-only analysis; no code was built or run.
It builds on the elab part 3 review (`docs/reviews/code-review-elab-rest.md`,
F2 and F16) and doesn't repeat it. All line numbers are on `main` at
`b42f164bf`.

## Summary

**What users get.** A program that checked before SW-1564 can now fail with
a confusing "settled as the empty row before the callback's type was known"
error. The fix makes the early settle safe. It also unblocks SW-1581,
without the guesswork, if we still want SW-1581.

**Findings.**

- **F2 is confirmed by reading.** `comp_app` settles the call's row before
  it retries the row comparisons the call itself put aside. A callback whose
  type only becomes known during the call can then hit `E-ABILITY` in an
  effectful function. I haven't run it. §1 has the example the implementation
  lane should run first.
- **F2 isn't the cause of the `List.cross` failure, as far as I can tell.**
  `List.cross` has no blocked callback, so nothing is put aside there. The
  experiment that broke it (SW-1564's lane transcript, 6 Nov, 06:04) also
  lacked the re-evaluation of the call's type after settling. The re-evaluation
  and the "row has abilities" guard went in together, in one edit (06:13).
  The error's shape points at a different missing rule: the settled unknown
  was not the call's own. §2 gives the detail. My confidence is medium; one
  run settles it.
- **The rule.** Settling a call's row to empty is safe only when five things
  hold: the unknown is the call's own, the call's postponed comparisons have
  been retried first, the unknown is not in the result type, the settle is
  recorded, and the type is re-evaluated after it. The committed code keeps
  two of the five (§4).
- **Recommendation.** One helper in `rows.rs` that checks all five, used by
  `comp_app` now and by `settle_let_lambda`. Then try SW-1581 again on top
  of it, as an experiment. Making the decision at the end of the declaration
  instead (design B, §6) is cleaner in principle. It changes the term shape of
  every lift, though, so it isn't worth it for one site.

## 1. The ordering, in plain words

When you call a function such as `List.map` that takes a callback, the
function's effects (its *row*) are the callback's effects. While the call is
being checked, the row is an unknown, `?e`. Usually checking the callback
decides it: a pure lambda leaves it open, and a callback that performs `Log`
fills it in.

Sometimes the callback's type can't be read yet. In the reject example
`map-callback-effectful-later.sw`, `answer` returns `Answer ?flag`. That type
is a computation that performs `Log` when `?flag` is `True`, and a plain
`Nat` otherwise. While `?flag` is unknown, the unifier can't decide whether
`?e` is empty or `{Log}`. So it puts the comparison `CompIn ?e ?b ≟ Answer
?flag` aside (`rows::postpone`, `rows.rs:223`) to retry later.

SW-1564 added a step at the end of `comp_app` (`effects.rs:3626-3630`).
"Every argument is checked and the call's row is still unknown, so none of
them performs anything: settle it as empty." The premise is wrong while a
put-aside comparison still mentions `?e`. The argument that fixes `?flag`
may already have been checked, but the comparison isn't retried until the
end-of-declaration rounds (`rows.rs:329`). By then `?e` is empty.
`settled_first` (`rows.rs:426`) sees an empty row against `{Log} Nat` and
reports `settled_too_early` (`rows.rs:484`).

**Example (to run first in the implementation lane).** This uses the
declarations of `examples/reject/map-callback-effectful-later.sw`, in an
effectful function, so that the row has abilities and the settle fires:

```
def logA (numbers: List (Tagged True)): {Log} Nat :=
  List.length (List.map numbers answer)
```

- **Before SW-1564:** `List.map`'s row stays `?e`. Lifting it into `{Log}`
  makes it `{Log}`. The end-of-declaration retry then finds `Answer True =
  {Log} Nat` against `CompIn {Log} ?b`, which holds. It checks, and `say`
  runs.
- **After SW-1564:** `?e := Empty` at the end of the inner `comp_app`.
  Retrying gives `E-ABILITY` "settled as the empty row (pure) before the
  callback's type was known".

That is my reading. If `numbers` fixes `?flag` before `answer` is compared,
nothing is put aside, and the example checks. In that case, use the
`countLater` shape (the flag fixed by a later argument of the same call,
`List.map2`-style, or by a named argument) to make the comparison wait.

The fix is the one `check::pure_first` (`check.rs:1774-1783`) and
`no_effect::pure_as_plain_calls` (`no_effect.rs:85-88`) already use. Note
`row_constraints.len()` on entry, and run `retry_rows_from(first_new)` to a
fixpoint before looking at the row.

## 2. Is F2 the reason `List.cross` broke? Mostly not

What the record shows (SW-1564's lane transcript, in this session's
subagent logs):

1. **06:04.** The settle was unguarded (no `row.labels.is_empty()` check),
   and `ty` was **not re-evaluated** after `settle_empty`. Loading std failed:

   ```
   std/List/Toolkit.sw:805:84
   def List.cross (xs: List a) (ys: List b): List (Pair a b) := List.flatMap xs (x => List.map ys (y => MkPair x y))
                                                                   ─────────── the inner List.map ───────────
   expected `Comp Effect.NoOp Effect.NoRes (List (a, b))`, but this has type `List (a, b)`
   ```
2. **06:13.** In one edit, the lane added both the labels guard *and*
   `cx.eval(&cx.quote(&ty)?)` after the settle. Everything passed. Nobody
   tried the unguarded settle with the re-evaluation.
3. The lane's later explanation ("the outer expected type then rejected it")
   says it didn't trace the comparison. The SW-1564 reviewer couldn't
   reproduce the failure either.

Why I think F2's mechanism isn't involved:

- **Nothing is put aside in `List.cross`.** Every callback type comes from a
  written signature: `flatMap`'s `a → {e} List b` and `map`'s `a → {e} b`.
  The lambda bodies are a call and a constructor. None of them is a
  definition stuck on an unknown, so `row_rule` (`unify.rs:537`) decides
  every comparison at once and never reaches the `blocked` branch (high
  confidence).
- **The stale type matters.** `force` re-reduces a value only when its head
  is a solved unknown (`needs_forcing`, `core/src/value.rs:1796-1801`).
  `CompIn ?e T` is a definition head with the unknown in its spine, so after
  `?e := Empty` it stays `CompIn ?e T` until it is quoted and evaluated
  again. Without the re-evaluation, `comp_parts` still returns a computation
  (`effects.rs:523`), and the call goes through `lift` rather than `done`
  (`effects.rs:3632-3633`). Read directly; high confidence.
- **The error's type names a closed empty row.** `Comp NoOp NoRes T` is what
  `done` builds for a row with no abilities and *no tail*
  (`effects.rs:2615-2619`, via `comp_type`). A bare `{?e}` gives `doneIn ?e`
  instead (`effects.rs:2598-2605`). So when the inner call was finished,
  `lift_plain` → `align` → `refresh` (`effects.rs:1289`, `1190-1192`) saw the
  *enclosing* row, `{?e0}` (the `flatMap` lambda's body row), as already
  empty. Meanwhile `comp_app`'s own `row` argument, taken before the settle,
  still said `{?e0}`.

That fits one story. **The unknown the inner call settled was, or had been
linked to, the enclosing lambda's row `?e0`.** Settling "the call's row"
then settled the row of the surrounding lambda from the inside. Everything
built afterwards, against the stale `row`, disagrees with the lambda's
codomain, which is now `List (a, b)`. In a row with abilities, the
enclosing row is never a bare unknown, so the labels guard hides this case.
It doesn't fix it. Exactly how `?e2` came to share `?e0` I couldn't pin
down by reading (medium confidence). Candidates are `align`'s
"open-to-open" case (`effects.rs:1246-1255`) and lambda checking against
the parameter type. **The implementation lane's first step is to check this:**
drop the labels guard, keep the re-evaluation, and log whether the settled
meta is the enclosing row's tail.

`pure_as_plain_calls` already guards against this. It only treats a row as
the line's own if its unknown was made after the line started
(`m >= first_meta`, `no_effect.rs:96-102`): "One made before it ... may
still become an effectful one."

## 3. The invariant

A row unknown `?e` may be settled to the empty row before the end of the
declaration only when all five of these hold:

- **I1, own.** `?e` was made for this expression: its meta id is at least
  the meta count on entry, and it is not the enclosing row's tail. Settling
  someone else's row is a decision about code we haven't seen.
- **I2, retried.** Every row comparison put aside since entry has been
  retried to a fixpoint, and no comparison still kept *from entry onwards*
  mentions `?e`. A kept comparison that mentions `?e` means a callback's
  type is still unknown, and the decision isn't ours yet. Comparisons put
  aside before entry belong to outer code. If one of them mentions `?e`,
  then `?e` isn't ours (I1).
- **I3, not in the result.** `?e` doesn't occur in the result's value type
  (`row_in_result`, `effects.rs:3692`). There the expected type decides it.
- **I4, recorded.** The settle runs inside `rows::settling_empty`
  (`rows.rs:110`), so a later error names this call (`settled_early`,
  `explain_defaulted`).
- **I5, re-evaluated.** Every type value held across the settle is quoted
  and evaluated again before it is inspected (see the `force` point in §2).

If any of I1 to I3 fails, the row is left unknown. Lifting and
end-of-declaration defaulting (`default_rows`, `rows.rs:374`, after the retry
fixpoint at `rows.rs:330`) then decide it, as before SW-1564. This doesn't
switch between two answers: either the call is plain, or the decision is
left to the existing rules. Nothing in it is a limit that runs out (D2543).

## 4. Where rows are settled today

| Site | What it settles | I1 own | I2 retried | I3 | I4 recorded | I5 |
|---|---|---|---|---|---|---|
| `comp_app`, `effects.rs:3626-3630` (SW-1564) | a call's bare `{?e}` → empty, when the enclosing row has abilities | **no** (the labels guard stands in for it) | **no** (F2) | yes | **no** | yes |
| `settle_let_lambda`, `effects.rs:1572-1592` (let, `2700`, `4641`) | an inferred let-lambda's result row → empty | yes (the lambda's own, from `inferred_row`) | **no**: callbacks inside the body may still be put aside | n/a | yes | yes (`1592`) |
| `check::pure_first`, `check.rs:1796-1800` | a pure context's value row → empty | yes (by construction: a pure context) | yes (`1781`) | n/a | **no** | yes (uses `value`) |
| `close_inferred_row`, `effects.rs:1599-1609` (`check.rs:2404`) | `{A \| ?t}` → `{A}` after a lambda body | yes | **no**: a later callback could add an ability to `?t` | n/a | **no** | callers re-read |
| `no_effect::pure_as_plain_calls`, `no_effect.rs:77` | nothing kept (a trial, undone) | yes (`first_meta`) | yes | — | — | — |
| `row_rule` apartness, `unify.rs:521-527` | `?e := Empty` when the other side can't be a `Comp` | — | — | — | — | — |
| `default_rows`, `rows.rs:374` | every noted row unknown still unsolved, at the end | — | yes (after the fixpoint) | — | reported as defaulted | — |
| `lift` / `settle_div`, `effects.rs:1085-1100` | a divergence unknown → `Total` | the callee's | **no** | — | **no** | `settle_div` re-reads |

The apartness rule and `default_rows` aren't guesses, so they need none of
this. The apartness rule only sets `?e := Empty` when the other side can
never be a computation. `default_rows` runs when nothing more can be learnt.

Two gaps besides `comp_app`:

- **`settle_let_lambda`** settles without retrying the body's postponed
  comparisons. Here is the shape that should go wrong (unconfirmed):
  `let f := (t: Tagged ?) => answer t` in a `{Log}` function, where a later
  argument fixes the flag. It has the same mechanism as F2, and the same fix.
- **`close_inferred_row`** closes an open tail, and **the divergence
  default in `lift`** picks `Total`. Neither is a settle to empty, but each
  makes a decision while comparisons may still be kept. I haven't found a
  program that breaks either one. I'd leave them, and say so in their docs.
  Changing them would be a larger change for no known user benefit.

F16 belongs here too. The fresh tails that `extend`/`extend_with`
(`effects.rs:1618`) and `align`'s open-to-open case (`effects.rs:1249`) make
are untyped `fresh_meta()`s and never noted. So `default_rows` never
defaults them, and `settling_empty` never sees them. A call whose row has
been extended has a fresh, unnoted tail. Settling that tail to empty is then
invisible to I4, which is another reason to type and note it.

## 5. The fix

Add one helper, `rows::settle_own_empty(cx, entry: Entry, ty: &Value) ->
Result<Value>`. `Entry` holds the `row_constraints` length and the meta count,
taken at the start of the expression. The helper does five things:

1. `while cx.e.retry_rows_from(entry.rows)? {}` (I2). An error from the
   retry is the user's error, as it is in `pure_first`.
2. Returns `ty` unchanged unless `unknown_bare_value(ty)` is `Some`, the
   tail's meta id is `>= entry.metas` and isn't the enclosing row's tail
   (I1), no kept comparison from `entry.rows` mentions it (I2), and
   `row_in_result` is false (I3).
3. Runs `settle_empty` inside `settling_empty` (I4).
4. Returns `cx.eval(&cx.quote_folded(ty)?)?` (I5).
5. Gets a doc comment stating the invariant, so the next site that settles
   uses the helper.

Then, in order:

- **`comp_app`** takes `Entry` on entry (before the head and the arguments
  run) and calls the helper where `effects.rs:3626-3630` is now. It keeps
  the `row.labels.is_empty()` guard for now. Removing it is SW-1581's
  question (below), not this fix's.
- **`settle_let_lambda`** takes the entry from its callers (`effects.rs:2690`,
  `4636`) and retries before settling.
- **`pure_first`** wraps its settle in `settling_empty` (I4 only).
- **F16:** `extend` and `align` make their fresh tails with `fresh_meta_of`
  the `Effects` type and `note_row_meta` them.

**SW-1581 afterwards (an experiment).** Drop the labels guard, so the helper
also runs when the enclosing row is a bare unknown, and run `List.cross`.
With I1 in place, `List.cross` should check: the inner call's row is either
its own and settles harmlessly, or it is `?e0`'s and is left alone. Only then
try settling at the end of `comp_check_in` and `comp_infer`. The ticket
doesn't say which user program SW-1581 would help. If the experiment finds
none (no changed hash outside the four SW-1564 already changed, no AoC or
example gain), close SW-1581 (D2810).

**How we'd know it works.**

- **New accept example, `examples/accept/row-settled-after-retry.sw`:**
  `logA` from §1, plus a `countLater`-shaped variant inside `{Log}`. It must
  fail on `main` and check on the lane. If `logA` already checks on `main`,
  F2 isn't reachable that way: record that on the ticket, and keep only the
  variant that fails.
- **New reject example, `examples/reject/row-settled-early-named.sw`:** a call
  whose row the helper settles, followed by a late effectful callback. Its
  snapshot must show the "the row of this call was set to the empty row"
  label at the call (I4). Today it is missing for `comp_app`'s settle.
- **SW-1581's case:** once the guard is dropped, std's `List.cross` checks
  (`std_files_check` or the prelude hash test). If it doesn't, the log from
  §2's first step says which invariant was missed.
- **Unchanged:** `examples/accept/pure-fold-in-parse-function.sw` and
  `row-in-result-type-call.sw`, the reject examples
  `map-callback-effectful-later.sw`, `row-stuck-callback.sw` and
  `row-defaulted.sw`, and the four effect-example hashes SW-1564 changed.
- **Unit test in `rows.rs` tests:** `settle_own_empty` leaves an unknown
  alone when a kept comparison mentions it, and when it was made before
  entry.

## 6. Designs compared

- **A. Settle early, under the invariant (recommended).** It is the
  smallest change. It keeps SW-1564's benefit (a pure fold in a `{Parse}`
  function is a plain call, which `Parse.readsDone` needs). One helper holds
  the rule, so the next site can't half-implement it, as this one did. It
  costs a retry pass per effectful call with a callback. The pass is bounded
  by the comparisons the call itself put aside, usually none, so it costs
  nearly nothing. What it rules out: an early settle where any comparison
  still mentions the row. Such a call is lifted and decided at the end, as
  before SW-1564, so in those rare cases the pure fold is a step of the
  enclosing row again.
- **B. Never settle early; decide at the end.** The lift would keep `?e`
  open (`liftIn ?e c`), and `default_rows`, which already runs after the
  retry fixpoint, would make it empty. This keeps I1 to I3 by construction.
  It means every lift into a row with abilities produces `liftIn ?e …`
  instead of solving the tail (`align`'s `solve_tail` branch,
  `effects.rs:1257`). That changes the kernel terms of most effect programs,
  so it needs Opus review (D2364). `liftIn Empty c` must also reduce to `c`
  wherever proofs look at it (`Parse.readsDone`). That's a much larger change,
  for the same user-visible result as A.
- **C. Keep today's code and only add I4.** Errors would point at the call,
  but the program in §1 would still be refused. That only explains the bug.

Lean has nothing like this, since effects there are monads chosen by type.
Koka's row inference (Leijen, "Koka: programming with row-polymorphic effect
types", 2014) generalises open rows at `let` and closes them only at the
outermost type, which corresponds to B. Its rows never meet types that
compute to effects (our `Answer ?flag`), so it never needs I2. GHC's
constraint solver keeps "touchable" unknowns per implication. Its rule that
only the level that made an unknown may default it is I1.

## Questions for Matt

- **D2810:** after the fix, do we still want SW-1581 (settling at the end of
  `comp_check_in` and `comp_infer`, and in rows with no abilities), or close
  it unless the experiment finds a program it helps? [rec: experiment only,
  and close it if there's no user-visible gain, because the ticket names no
  user program and each new settle site is a place for this bug to come
  back]
- **D2811:** when a call can't be settled early because a callback's type
  is still unknown (I2), should it quietly fall back to the pre-SW-1564
  behaviour (lifted, decided at the end), rather than give an error asking
  for the callback's type? [rec: fall back, because the old behaviour was
  correct, only less tidy, and an error would refuse programs that checked
  before SW-1564]

## Tickets to file

1. **Row settling under one rule (F2, F16).** This is SW-1926's
   implementation; it replaces the review's ticket 2. First, run §1's
   example and §2's diagnostic, and record both on the ticket. Then add the
   `settle_own_empty` helper, use it in `comp_app` and `settle_let_lambda`,
   add `settling_empty` in `pure_first`, and type and note the fresh tails.
   Add the two examples and the unit test. **Opus** (core inference), 60-75
   min. Tests: `task test:one` for `rows::tests`; the
   `accepted_`/`rejected_examples` tests filtered to the new examples and the
   unchanged list in §5; `hash_stability` for the effect examples;
   `aoc_answers year2020_day18`. It goes first.
2. **SW-1581 experiment.** After 1 and D2810. Drop the labels guard, run
   std (`List.cross`), then try the `comp_check_in`/`comp_infer` sites and
   report which hashes change. Merge only with a user-visible gain;
   otherwise close SW-1581 with the finding. **Opus**, 45 min. Tests: the
   prelude/std check, `hash_stability`, and the effect examples.
3. **Document the two decisions left alone** (`close_inferred_row`, the
   divergence default in `lift`): one paragraph each on why closing or
   defaulting there is safe or accepted. **Sonnet**, 20 min, docs only. It can
   go with 1.

## What this note doesn't cover

- I didn't run anything (per the rules for this lane). §1's example and §2's
  shared-unknown story are readings, and the confidence of each is stated
  where it is made. The first step of ticket 1 is meant to confirm or refute
  them in a few minutes.
- F8 (`retry` losing comparisons on error) interacts with I2. A retry that
  fails partway would lose the comparisons the helper relies on. It's the
  review's ticket 3, and it should land before or with ticket 1.
