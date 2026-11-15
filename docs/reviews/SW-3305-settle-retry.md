# SW-3305 review: retrying a call without the type arguments `settle_from_expected` gave it

Reviewer: Opus, 15 Nov 2026. Branch `lane/SW-3305` (c84283e65, 0f5763e14)
against `main` at adc398ffe. Probes ran on two binaries:

- **BR**: the worktree's release binary (built 02:53:36, after the last
  change to `check.rs` at 02:50).
- **MAIN**: the main checkout's release binary. It has SW-3282's settling
  but no retry.

I had no binary from before SW-3282. To stand in for "no settling", each
probe has an `…ok.sw` twin that writes `[t := Nat]`. A non-empty supply
turns settling off, and `Nat` is what the parser argument gives `t` anyway.

The probe files are in the review's scratch folder: `p1*.sw`, `p2*.sw`,
`e1*.sw`, `e2.sw`, `gen.sh` (`deep*.sw`), `genf.sh` (`f*.sw`) and `run.sh`.

## Verdict

Mergeable. The change is sound: nothing wrong can be accepted, since the
final comparison and the kernel still run. Every new counter and flag is
put back on every path. g5 and g6 are accepted, and BR rejects nothing
that MAIN accepts.

The change doesn't fully deliver its own claim, though. The doc comments
say that "a program the guess rejects must still be accepted", and the
ticket wants that by construction. There are two places where a failure
counted as speculative (`settle_trial`) turns out to be final without the
promised recheck:

- A propagation plan whose fall-back is `propagate_failed`.
- A held argument whose application then fails its comparison with the
  expected type.

I built a probe for each (S1). Each needs a goal that matches only by
unfolding (S1 of the SW-3282 review), nested in one of those two places.
No std or AoC shape does that.

The guard (`parameter_type_is`) is the right test. Stitchwort has no
cumulativity, so conversion of the parameter's type with the sort is
exact.

A failing nested chain now costs more than linear time (S2). Error reports
when settling was itself the mistake can point at a correct argument (S3).

A simpler design exists: one retry per declaration (Q5). It would close
both holes, remove three of the four new `Decl` fields and the
held-argument recheck, and cost failing declarations at most twice the
work.

## Must-fix

None.

## Should-fix (ticket)

**S1. Two speculative failures are never rechecked, so programs the retry
should rescue are still rejected.**

*(a) Propagation plan, `propagate_failed` path* (`p1b.sw`):

```
def double (n: Nat): Nat := n + n
theorem wrap ∀ [k: Nat] (y: double k <= 0) (x: Ph Char k): Ph Char k := x
theorem p1b: Ph Char 0 := wrap (Nat.leRefl 0) (ph natSrc 0)
```

- **What happens.** `wrap` gets a plain plan, `k := 0`. Inside
  `plan.apply` (`settle_trial`), `ph natSrc 0` is settled with `t := Char`
  and fails. Its retry is skipped. The plan fails, and since it isn't
  by-arguments, `propagate_failed` re-elaborates with bare `infer`. There
  `y` meets `double ?k ≤ 0`, which can't be solved, and fails.
- **BR** rejects it with E-TYPE-MISMATCH at `Nat.leRefl 0`, a correct
  argument, with a note saying `k` wasn't worked out.
- **`p1bok.sw`** (no settling) is accepted. So is the plan with `x`
  unsettled.

`propagate` throws away `settle_trial`'s "skipped" flag. Its comment says
"a failure is elaborated again from the start below, so retries … would
be wasted". That holds for the by-arguments path (`after_arguments_failed`
goes through `fallback_inferred`, which has the retry). It doesn't hold
for `propagate_failed`: re-elaborating without propagation is a different
procedure, not the same work done again. This is the same weakness as
M1 in the SW-3281 review.

`p1.sw` is the same shape with `y` given as `rfl` (a proof search, held to
the end). BR accepts it and MAIN rejects it, so the retry does help where
the bare path copes.

*(b) Held argument, then the comparison fails* (`p2.sw`):

```
theorem outer ∀ [k: Nat] (x: Ph Char k) (m: Nat) (h: double k = m): double k = m := h
theorem p2: 0 = 0 := outer (ph natSrc 0) 0 rfl
```

- **What happens.** `x`'s check is a trial, because its type has an
  unknown and the expected type is known. Inside it, the settled `ph`
  fails and its retry is skipped. In `explicit_arg_failed`, `unsolved_in`
  finds `?k`, so `x` is held, and the skipped flag is dropped. Then
  `finish_application`'s comparison of `double ?k = ?m` with `0 = 0`
  fails, and it returns `first_error`: the settled error. Nothing
  rechecks `x`.
- **BR** rejects it with "expected `() → {Src Char} ?1`" at `natSrc`.
- **`p2ok.sw`** is accepted. Checked in place, `x` solves `k := 0` by
  unfolding.
- **Control `p2c.sw`** (the result `k = m`, so the comparison succeeds):
  BR accepts it. The after-expected recheck isn't a trial, so the retry
  runs. MAIN rejects it.

Neither probe is a regression against MAIN: BR strictly improves on it.
They are gaps in the ticket's "by construction" claim. The fixes, cheapest
first. Each needs day 2 measured again, since the 6× came from exactly
these speculative places:

- **(b)** When `explicit_arg_failed` sees `skipped`, check the argument in
  place once more with `no_settling`, whether or not it would be held.
  That is what an unsettled checker does first anyway. Alternatively,
  keep the flag with the held argument, and recheck it with `no_settling`
  in `finish_application` before returning `first_error`.
- **(a)** When the plan fails with `skipped` set, apply it once more with
  `no_settling` before falling back.
- **Or** take Q5's per-declaration retry, which covers both.

Also correct three statements that currently overclaim: the
`fallback_inferred` doc comment ("must still be accepted"), the comment in
`propagate`, and `settle_trial`'s doc ("an argument whose failure is
final is rechecked").

**S2. A failing nested chain costs more than linear time.** `genf.sh`
builds `step charSrc 0 (step charSrc 0 (… base))`, where `step ∀ (p: () →
{Src t} a) (n: Nat) (inner: Ph t n): Ph t n`, and `base` is the one
wrong proof (`Ph Char 1`). Times are wall-clock and include loading std
(about 0.3 s):

| depth | BR | MAIN |
|---|---|---|
| 10, 20, 40 | 0.32–0.34 s | 0.32–0.33 s |
| 100 | 0.73 s | 0.32 s |
| 200 | 2.89 s | 0.36 s |
| 400 | 25.6 s | 0.73 s |

The correct chain at depth 400 takes 0.48 s on BR and 0.45 s on MAIN, so
only errors pay.

My reading, not traced: each level's held-argument check fails with a
skip. `explicit_arg_failed` rechecks the whole subtree with
`no_settling`, the error goes up, and the next level skips and rechecks
its own subtree again. That alone is quadratic, and the unsettled
re-elaboration of a failing subtree adds more. Real chains are under 20
deep (day 2 has 7 levels of `runsBind`), so this is cheap today. But it's
on the path every user's mistyped parser proof takes, and in the LSP on
every keystroke while it's broken.

Possible fix: once one recheck in a declaration has failed, don't
recheck again in outer levels. For example, raise `no_settling` for the
rest of the failing path, or have the error carry "already tried
unsettled". Q5's design doesn't have the problem.

**S3. When settling was the mistake, the settled error blames a correct
argument.** `e1.sw` is `theorem e1: Ph Char 0 := ph natSrc True`. The
real error is `True` where a `Nat` is expected, and the goal matches
`Ph Nat 0` by unfolding.

- **BR** reports at `natSrc`: "expected `() → {Src Char} ?0`, but this
  has type `() → {Src Nat} Nat`", plus the `?0` note from SW-3282's S2.
- **Without settling** (`e1ok.sw`): "expected `Nat`, but this has type
  `Bool`" at `True`. That's the right blame.

`e2.sw` (`ph natSrc 1`, where the goal really doesn't match) gets the
same `natSrc` blame. There, either message is defensible.

This is the price of 0f5763e14's choice, and the choice is still right on
balance: g2, g8 and r1 are the common case, and there the unsettled error
blames the whole call or the numeral `5`. No location rule separates the
two: g8's unsettled error is also in a later argument, so "the unsettled
error is further on" doesn't identify the case.

Cheap improvement: when both attempts fail and the settled error is
given, add a note saying where `t` came from. For example: "`t` was taken
as `Char` from the expected type `Ph Char 0`; without that, the error is
at …" with the unsettled error's span. Then the reader in e1 gets both.

## Nits

**N1.** `settled_failed` checks `settle_trial > 0` before `fatal(&e)`, so
it sets `settle_skipped` for fatal errors too. That's harmless, since
fatal errors pass every handler. Swapping the two checks would match
`explicit_arg_failed`.

**N2.** `explicit_arg` repeats `settle_trial`'s body inline, for stack
reasons. A comment on `settle_trial` saying that `explicit_arg` mirrors it
would stop the two drifting apart.

**N3.** The ticket note's "an argument whose failure is final is
rechecked" should say "a held argument's in-place failure where nothing
is left unknown". S1(b) is the other kind of final.

## Questions from the brief

1. **Correctness and restore paths.** Every increment has its decrement
   with no `?` and no early return in between:
   - `no_settling`: in `settled_failed` around `fallback_inferred`, and in
     `explicit_arg_failed` around `check_arg`.
   - `settle_trial` and `settle_skipped`: in `settle_trial`, and inline
     in `explicit_arg`, where the restore runs when `outer` is `Some`,
     which is exactly when the increment ran.
   - `settled`: `infer_expecting` saves it with `replace(false)` and
     restores it after `infer` on every path. 0f5763e14 removed the old
     `?` on `force` there. `settled` is only set in
     `settle_from_expected`. That runs only when `Held::start` matched
     `app_expected`'s key, and `app_expected` is set only inside
     `infer_expecting`. So the flag always has an owner, and the leftover
     check holds.
   - `settle_skipped` is set only while `settle_trial > 0`, so some
     wrapper restores it.
   - A stale `settled = true` (say from `retrying`'s first try) can only
     cause an extra retry.
   - **Wrong acceptance:** impossible.
   - **Rejecting what MAIN accepts:** none found. Every probe BR rejects,
     MAIN rejects too.
2. **The `settle_trial` skip.** It isn't complete: there are two final
   failures with no recheck, S1(a) and S1(b), both probed. The
   by-arguments plan path and held arguments that are rechecked after the
   expected type are fine (`p2c.sw`).
3. **`parameter_type_is`.** It is the right test. The core has no
   cumulativity (`docs/core.md`), so a goal argument fits the type
   parameter exactly when the definition's parameter type, instantiated
   with the goal's earlier arguments, converts to the parameter's sort.
   - *Wrongly allows:* nothing. A well-typed goal's argument has that
     type, and a well-sorted guess that turns out wrong is the retry's
     job.
   - *Wrongly blocks, cost only:* a parameter type that is still an
     unsolved unknown (`Dep ?k …`). No correctness impact.
   - `def_ty` on `call_parts` ids is safe: those are always definitions.
4. **Errors.** With the guard, g6's ill-sorted row is gone
   (`reject/settle-from-expected-dependent-mismatch.sw` blames the whole
   call, as it should). Where settling was the mistake and the program
   has another error, the settled error blames a correct parser argument
   (S3, `e1.sw`).
5. **A simpler design.**
   - *A soft hint the unifier may drop:* no. The clash shows up as a
     rigid row mismatch deep inside an argument's check, long after the
     hint was used, so dropping it means backtracking anyway. And the
     speed comes from rows being literal rather than solved unknowns,
     which a hint wouldn't give.
   - *One retry per declaration:* this would be simpler. Settle freely,
     with no retry inside. If the declaration fails and anything was
     settled, re-elaborate the whole declaration once with `no_settling`,
     and report the settled error if both fail. That keeps one counter
     and a "settled somewhere" bit. `settle_trial` and `settle_skipped`
     go, and so do `explicit_arg`'s inline trial and
     `explicit_arg_failed`'s recheck.
     - It gives "accepted whenever the unsettled checker accepts" by
       construction, both S1 holes included.
     - Failing declarations cost at most twice as much (S2 gone), and
       successful ones are unchanged.
     - Costs: a broken declaration in the LSP is elaborated twice, and a
       declaration where settling helps in one place and hurts in another
       falls back to unsettled everywhere: correct but slower.
     - Untested: whether everything a declaration does (warnings,
       lifted local definitions, the queue) is undone by one `Snapshot`
       at that level. I'd ticket it as an alternative, for Matt or the
       orchestrator to choose against fixing S1 and S2 in place.
6. **Stack.**
   - The plain-plan nesting probe (`gen.sh`: `idp (idp (… base))` with
     `idp ∀ [k: Nat] (x: Ph Char k): Ph Char k`) checks at depths 50,
     100, 200, 300, 500, 800 and 1200 on both binaries, with no overflow
     and no difference.
   - The `settle_trial` frame on the `propagate` path doesn't show up at
     any depth I tried.
   - The lane's own figures (nested settled calls 214 → 209, and 54/54
     and 42/41 under the 320 KiB guard) are a small loss, which I'd
     accept.
