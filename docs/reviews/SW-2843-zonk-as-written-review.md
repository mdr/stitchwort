# SW-2843 review: zonk reads solutions back as written

Opus paper review (D2364) of commit `57206efa6` on `lane/SW-2843`: core
`quote_as_written`, zonk substituting solutions with it, the unfolding
fallback under a 100,000-step side budget, goal assumptions stated as
written, `refold`'s `value_forms`, 1,035 of 5,974 std hashes moved, and the
Float.neg, abs and sub pins. Read-only: nothing was built or run.

**Verdict: no must-fix. Sound, and the pin updates are legitimate.** Three
should-fixes: a test for the case that motivated the change, errors that
aren't resource errors swallowed by the fallback, and a fallback that
unfolds the whole solution when only one call needs it. The verifier should
run the examples and an `aoc/` check over this lane, because some of the
elaborator's "does this mention an unknown" checks now see more unknowns.

## Summary of the change

`Readback::AsWritten` (`crates/core/src/value.rs:3187-3191`) is
`Readback::Folded` without the `matches_at_once` exception: every
`Value::Call` is read back as `Term::Def(id)` applied to its arguments
(which are themselves read back as written). A call that `Folded` used to
force (`if True then a else b`, `List.length (Cons x xs)`,
`countDown 100000 []`) now stays a call. Zonk (`unify.rs:3294-3315`), the
goal statement (`assume.rs:239-242`) and `value_forms` use it.

## (1) Soundness and meaning

**OK: the kernel sees convertible terms with the same meaning**
(`value.rs:3187-3205`). Each new subterm is `Term::Def(id) args` for a
`Value::Call(id, spine, _)` that `Folded` would have forced. The two are
delta-equal, and the kernel computes calls unglued. Every call that
`AsWritten` keeps but `Folded` didn't passed `matches_at_once`, which needs
`body_seen(g, id)` (`value.rs:943-946`): the definition has a visible body,
so it is a real, defined global. No new kind of reference reaches the
kernel: calls to pending definitions, hidden opaque ones, and fields of
calls (`is_call_field`) were already written as calls by `Folded`. So
the kernel accepts the term iff it accepted the old one, up to resources.

**OK: syntactic checks in the kernel only get stricter.** Positivity
(`crates/core/src/check.rs:3881-3912`) is syntactic: a member under a
`Term::Def` call is `Occurrence::Inside(Other)`, which it rejects. A
constructor field whose type is solved to an at-once call around the type
being defined (`if True then T else Nat`) used to be computed to `T` and
accepted. Now it is rejected. That can only cause regressions, never
unsoundness, and it is unlikely: such a field type has to come from a
solution, not from what the user wrote. The same goes for any syntactic
termination or structural check: a kept call adds call sites, so a checker
that looks at calls can only refuse more. A call to the definition being
elaborated can't be new here: it has no visible body yet, so `Folded` kept
it too.

**OK: erasure and lowering.** Value-level solutions (dictionaries, explicit
`_`) may now carry a call that runs at runtime instead of its precomputed
step. It is the same function and the same result. Type and proof
positions are erased as before.

**OK: hash-consing and caches.** Content hashes move: 1,035 entries in the
prelude snapshot. Check caches are keyed by content hash, so they
invalidate themselves. Nothing compares hashes across the change except
the pins (see (2)).

**NOTE: elaborator queries that ask "does this mention an unknown" now see
more unknowns.** These callers zonk with `keep = all`:
`interfaces.rs:1416/1423` (`unsolved_in`, used by `check.rs:3050/3149/3181`,
`interfaces.rs:989/1346/1349/1671`, `rows.rs:474`), `effects.rs:3987`,
`matching.rs:797/1871`, and `interfaces.rs:1736-1750`
(`find_ready_dictionaries`). With `keep = all` the fallback in
`unify.rs:3304` never fires, so the zonked term keeps an unknown that sits
in an argument an at-once call drops. Before the change, `Folded` computed
that call away. These checks over-approximate, which mostly means waiting
longer. But some choose a different path:

- `check.rs:3050`-`3181` branch on `unsolved_in(dom)`.
- `find_ready_dictionaries` scans only syntactic `Term::Data(_, args)` for
  unknowns to leave to unification. A `Data` inside a kept at-once call is
  missed, so its dictionary unknown is solved by instance search instead.
  That gives a valid instance, but possibly earlier or a different one.
- `stuck_term` (`interfaces.rs:1703`) now also sees a projection applied to
  a constructor dictionary that `Folded` used to compute. That means more
  `refresh`es of equation types. Harmless, but it costs time.

Std elaborates and sf/ is unchanged (per the commit), so none of this
showed up there. It is a reason for the verifier to run the four example
kinds and an `aoc/` check over this lane.

**NOTE: unfinished-proof reliance only gets more conservative.** SW-2837's
`relies_on` reads terms. A kept call to a goal-relying definition marks
its user as relying, where the computed step might not have mentioned it.
That is safe in the right direction: more "unfinished", never fewer.

**NOTE: `lift.rs:1100` gets a superset of free variables.** The union over
`value_forms` now includes the as-written form, which can mention variables
the folded and unfolded forms drop (`const 0 y`). `scope` then grows for
every form, so the folded and unfolded forms are refolded only at that
larger scope. The result is still correct, but in rare cases fewer `let`s
fold back.

## (2) The Float pins

**OK: the pin updates are legitimate** (`crates/core/src/pins.rs:121,125,157`).

- The lane changes no std source: `git diff main...57206efa6 --stat`
  touches no `.sw` file, and `Float.sw:195-238` is untouched.
- The snapshot diff shows what moved in the closures of `neg`, `abs` and
  `sub`: the theorems `clearValid`, `clearValidFrom`, `flipValid`,
  `flipValidFrom`, `flipNotNaN(From)`, `flipFlip(From)` and `highBound`
  (proofs elaborated with `omega` and `match`, whose metavariable solutions
  are now written as written), and the definition `negFrom`, which mentions
  `flipValid`. The computational parts did not move: `Float.isNaN`,
  `flipSignBits`, `clearSignBits`, `Float.make`, `Float` and `Float.add`
  (whose pin is unchanged) keep their hashes. `sub` moved only through
  `neg`.
- A content hash covers everything a declaration mentions, proofs
  included (`pins.rs:11-13`). So a proof-only change upstream moving a
  pinned hash is exactly what the mechanism reports. The natives
  (`float.rs`) compute bits from bits, and `Float.make`'s validity proof is
  irrelevant to them.

One gap: the evidence is by elimination over the snapshot, not direct. The
pin doc (`pins.rs:17-19`) asks that someone check the natives against the
changed declaration. `proofless_hash` (`crates/core/src/hash.rs:134`, shown
by `stitchwort trial-edits` through `declhash.rs`) would settle it in one
step: if the proofless hashes of `Float.neg`, `abs`, `sub` and `negFrom`
are unchanged, the move is proofs only. **SHOULD-FIX (cheap):** the
verifier runs that comparison, and the ticket records the result next to
the pin update. If a proofless hash did move, stop and look at
`negFrom`'s body. I don't expect that.

## (3) The 100,000-step fallback budget

**SHOULD-FIX: a real but narrow regression path** (`unify.rs:3304-3315`).
Before, an unknown inside an at-once call's dropped argument (`if True then
A else ?B`) vanished during the folded read-back, with no fallback. Now
the as-written form keeps it, so the fallback fires. The fallback unfolds
the **whole** solution (`quote(g, level, &value)`), not the one call, with
`size: 20_000` nodes and `frames: 10_000`. So a solution that is large
when fully unfolded (a type over a long list, say) and has one such
unknown now reports **unsolved**. Before, it elaborated: `Folded`
computed only the at-once calls, within the declaration's 10^10-step
budget. Std and sf/ show no instance, but aoc/ and examples are untested
here.

Is the limit principled? 100,000 work matches `cheaply` (`unify.rs:3017`),
and attempt limits are the same in every build. That's sensible. But
`..Limits::default()` brings in a stack limit measured from the current
position (1.5 MiB). SW-962 is why `cheaply` pins its own `stack` and
documents it. The readback is iterative, so this probably never binds, but
the limits should say so. The better fix, and the principled one, is to
fall back **per call**: in `AsWritten`, read a call back `Folded` (or
unfolded) only when its arguments mention an unsolved, non-kept unknown.
That computes exactly where an unknown has to be lost, makes the budget
almost never matter, and keeps the rest of the solution as written. This
could be a follow-up ticket, provided the verifier's aoc/examples run is
clean.

**SHOULD-FIX: non-resource errors are swallowed** (`unify.rs:3309-3313`).
`if let Ok(unfolded)` drops every error from `quote`. The old code
propagated them with `?`. An internal error, or a `Cancelled` (`aside`
restores `exhausted`, so the next `step` raises it), now comes out first
as `ZonkError::Unsolved(m)`, which may become a user-facing "unsolved"
diagnostic. Swallow only resource exhaustion and propagate the rest.

## (4) refold / `value_forms`

**OK** (`unify.rs:3049-3062`, `3320-3337`). Replacing any form of a
`let`'s value by the `let` variable is a zeta step, so it is correct for
every form that denotes the value at that level. The as-written form does,
and it is now the form zonk produces, so it should be listed first. The
dedup with `same_term` keeps the list at three at most.

**NOTE:** `value_forms` computes the unfolded form first
(`unify.rs:3050`). Under `cheaply`, a value too large to unfold makes the
whole call fail, so no form is refolded, not even the cheap as-written
one. Since zonk now writes solutions as written, computing `as_written`
first and keeping the forms that fit would fold more `let`s back. This is
an optimisation, not a bug: refold was already all-or-nothing.

## (5) Performance

The likely effects, all unmeasured:

- **Zonk gets cheaper:** it no longer forces at-once calls (that was the
  E-RESOURCE).
- **Terms get smaller,** so hashing, caching and serialisation get cheaper.
- **The kernel may do more delta steps:** it now computes steps that were
  precomputed in the term. Usually lazily, and `f a ≡ f a` is often
  decided by the shared head.
- **Re-evaluating zonked terms in the elaborator** (`interfaces.rs:1417`
  `cx.eval`, the queue's re-zonks) builds fresh call cells, so the same
  steps run again.
- **`value_forms`** does three read-backs instead of two at every `let`, on
  every zonk pass, and `refold` compares against up to three forms. This is
  bounded by `cheaply`.
- **Each fallback `aside`** has its own budget of up to 100k steps, not
  charged to the declaration. Many unknowns, each needing it, could cost
  about n × 100k steps with no `E-RESOURCE`.

What Overmind or the verifier should time, main against the lane:

- std check (elaboration and kernel time separately, if the timings split
  them)
- `sf/ check --no-cache`: about 1.31 s on main per SW-2837's notes
- an uncached whole-`aoc/` check
- the benchmark's elaboration-heavy cases
- for the kernel specifically, a profile of the declarations with the most
  moved hashes: the Float theory and the `omega`-heavy files

## (6) Other

- **SHOULD-FIX: no test was added.** The commit changes no test file. It
  wants at least:
  1. a goal whose zonk used to run out (`countDown 100000 [] = []` stated
     as a goal or assumption, beyond `search_at.rs:230`'s use) elaborates
     without `E-RESOURCE`;
  2. an unknown only in an at-once call's dropped argument still
     elaborates (the `const 0 []` / `if True then A else _` shape), which
     pins the fallback.
- **NOTE: naming.** "As written" also covers calls the evaluator produced
  while unfolding (the calls inside a step's result), not only calls the
  user wrote. The doc at `value.rs:2874` says "every glued call", which is
  accurate. The name is fine as long as nobody reads it as source fidelity.
- **NOTE:** `docs/proposals/folded-calls.md` is updated. `docs/core.md`
  doesn't need to change: the kernel is untouched.

## Verdicts

| # | Where | Verdict |
|---|---|---|
| 1a | value.rs:3187-3205, kernel acceptance and meaning | OK |
| 1b | check.rs:3881 positivity, termination: stricter only | OK |
| 1c | interfaces.rs:1416-1750, effects.rs:3987, matching.rs:797/1871 see more unknowns | NOTE (verifier: examples + aoc) |
| 1d | relies_on more conservative; lift.rs:1100 scope superset | NOTE |
| 2 | pins.rs:121,125,157: proofs-only move by elimination | OK; SHOULD-FIX record proofless-hash check |
| 3a | unify.rs:3304: whole-solution fallback within 20k nodes can newly fail | SHOULD-FIX (per-call fallback) |
| 3b | unify.rs:3309: non-resource errors swallowed | SHOULD-FIX |
| 4 | value_forms / refold | OK; NOTE as-written-first |
| 5 | performance | NOTE: time std, sf/, aoc/, kernel split |
| 6 | no regression tests | SHOULD-FIX |
