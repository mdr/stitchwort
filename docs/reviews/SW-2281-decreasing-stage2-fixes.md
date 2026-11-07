# SW-2281: review of SW-2220 (decreasing stage 2 fixes)

Reviewed: merge `a89beb76a` (lane commit `dbbd7cf90`), which fixes F1, F4,
F6, F7 and F8 of [SW-2208](SW-2208-decreasing-match-fact.md). Read only: no
builds or tests run.

## Summary

The change is sound. Everything it affects ends up in definitions and
theorems the kernel checks (`kernel::declare_def` and `define_group` for
each twin and its `%same`), and none of the five changes can make the
kernel accept a false statement. The worst a mistake in them could do is
an internal error, which `plain_view_or_not` turns into the
`W-DECREASING-UNFOLD` warning and the unplain `f.unfold`. The lane's worry
about F7 is real, but it's harmless: helpers that an abandoned
`with_local_retries` attempt lifted are in `tables.lifted`, so they still
get twins. That wastes a few definitions, and a twin that fails costs the
whole plain view. The findings below are all low.

Top recommendations:

1. Make twins only of the helpers the final attempt lifted (R1).
2. State the invariant that F6's fallback relies on and check it:
   `rewind_globals` doesn't rewind `tables.lifted` or the records (R2).
3. Make the fallback loud in checked builds, not silent (R3).
4. Have the guard test check `f.unfold`'s shape, not only that the file
   loads (R4).
5. Fix the `twin()` comment, which describes a case F7 now rules out (R5).

| # | Finding | Severity | Confidence | Size |
|---|---|---|---|---|
| R1 | Helpers orphaned by `with_local_retries` still get twins | low | medium | S |
| R2 | `rewind_globals` leaves `tables.lifted` and `tagged_helpers` behind; the invariant isn't written down | low | high | S |
| R3 | F6's fallback is silent | low | medium | S |
| R4 | The guard test can't catch an equation left in `f.unfold` | low | high | S |
| R5 | `twin()`'s comment names a case that can't reach it; `twin()` searches all of `tables.lifted` for each helper | low | high | S |

## Answers to the brief's questions

**1. Can `dead_lets` after `post` drop a `let` a proof needs?** No.
`dead_lets` (`plain.rs:225`) drops a `let` only when its body doesn't
mention it. `Term::mentions` counts `Var`, and `Case`/`NumCase` scrutinee
indices too, through every subterm including annotations
(`core/src/term.rs:705`). The pass runs on `post`, the twin's or
`f.%plain`'s body, and never on a proof. The `%same` proof is built from
`marked` (`tree_proof`), and `hole_proof`'s `Let` case keeps the `let`
around the inner `H.%same` call, so the proof still has the value. The
proof's type then has the `let` and the stated type doesn't. The kernel
accepts that by zeta: the `let`'s body doesn't use it, and the `let` is
the transparent kind (`Term::Let`'s flag only says whether running skips
the value). The rewrite is bottom-up, so a chain of `let`s, each used only
by the next, all go, innermost first.

One side effect, which is fine: `needed` is now computed on the
dead-let'd `post` (`plain.rs:1091-1095`), so a parameter that only a
dropped `let` used leaves the twin too. Callers stay consistent, because
`post` drops arguments by the same `kept` (`twin_of`). A twin can now
exist where before `count == 0 && kept.len() == a` returned `None`, and
it's checked the same way.

**2. Do guards in the name check let the unnamed equation reach a proof it
shouldn't, or change the guard's meaning?** No. The check only decides
whether an unnamed expression scrutinee gets the hidden name `%found`
(`matching.rs:536-545`). `%found` is an `rfl`-proved `e = s`, so any proof
it reaches is a true proof, and the kernel checks it. The guard's `Bool`
term is unchanged apart from being under one more binder. Users can't
write `%`-names, and the warning path still treats `%found` as unnamed
(`matching.rs:1265`). SW-2208 F5 still applies: any proof in the arm can
use it, the guard included. Two false positives were there before and
stay harmless: a pattern variable whose name matches the definition's last
segment, and another definition with that same last segment. In both, an
equation nothing uses isn't captured. In the twin, `Rec::adapt` drops
every `%rec` proof wherever it sits (`plain.rs:312`), the guard's included,
so a guard-only use of `%found` doesn't keep the equation in `f.unfold`.

**3. Is F6's silent fallback safe?** Yes. `twin()` uses a record only when
settling it gives exactly the kernel's body (`plain.rs:1013-1016`).
Otherwise it uses the kernel's own body. Either way the body it works from
settles to the definition's real body, and `%same` is checked against
`Def(h)`. So a wrong record could at worst produce a lemma the kernel
rejects (an internal error, then the warning), never a wrong one. With
F7, a definition that isn't in `tables.lifted` returns before the record
is read, so the case the comment describes can't reach the check (R5). The
only way a stale record could still be seen is an id that appears in
`tables.lifted` but whose kernel definition was forgotten and replaced
(R2). The silence is a UX risk, not a soundness one (R3).

**4. Is the "abandoned attempt, then retried" gap real?** Yes, but
harmless. `with_local_retries` (`lib.rs:2481`) only clears metas between
attempts. It doesn't rewind the kernel or `tables`, so a `match` lifted in
a failed attempt keeps its `DefId`, its `tables.lifted` entry
(`lift.rs:761`) and its record. Each retry's helpers get fresh ids, so no
record is stale, but the orphans fall in `first_helper..`
(`decreasing.rs:1091`) and pass F7's check (R1). The other route, a kernel
rewind that reuses an id, goes through `rewind_globals`, and none of its
callers lifts a `match` inside the window it rewinds:

- `plain_view_or_not` (`decreasing.rs:1517`) pushes its twins to
  `tables.lifted` only after it succeeds.
- Equation generation (`equations.rs:2471/2476`, `induct.rs:356/363`)
  builds terms directly and never goes through `lift.rs`.
- `undo::Snapshot` doesn't touch the kernel.

So that route is closed today, but nothing enforces it (R2).

**5. Is everything new checked by the kernel?** Yes. The twins and their
`%same` lemmas go through `declare_def` and `define_group`, and
`f.unfold` is proved from them, so no term is trusted. `dead_lets`, the
name check, the records and the F7 filter only decide which definitions
get built and from what. What gets built is checked.

## Details

### R1. Helpers orphaned by `with_local_retries` still get twins (low, medium)

`decreasing.rs:1091` takes `helpers` as every definition from
`first_helper` on. Under `with_local_retries`, that includes the helpers
of every failed attempt, and F7's check (`plain.rs:996`) passes for them
because `lift.rs:761` pushed them to `tables.lifted`. `twin()` then builds
`H.%plain` and `H.%plain.%same` for each orphan. Nothing calls them,
because `mark` marks only calls in the step's body. That's two dead
definitions per orphaned `match`, each with a copy of its case tree. If
one of those builds fails without being fatal, `plain_view_or_not` throws
away the plain view for the live helpers too, with `W-DECREASING-UNFOLD`.
The same orphans already pass through `respects`, which iterates the same
range (this was there before the change).

**Fix.** Take `first_helper` at the start of the attempt that succeeds.
Alternatively, filter `helpers` to the definitions reachable from
`f.%step`'s body by `Term::Def`, which is also robust against any future
orphan source. S.

### R2. The invariant behind F6 lives only in a comment (low, high)

`rewind_globals` (`lib.rs:1136`) forgets kernel definitions but leaves
`tables.lifted` and `Active::tagged_helpers` alone. F6's exact records and
F7's filter are correct only while no caller lifts a `match` between
taking its mark and rewinding to it, which is true today (question 4).
If that changes, a stale `tables.lifted` id would pass F7 and land in the
record check.

**Fix.** In `rewind_globals`, debug-assert that no `tables.lifted` id is
at or past `mark.defs()`, or truncate `tables.lifted` there. Either one
turns the fallback into a pure invariant check. S.

### R3. F6's fallback is silent (low, medium)

If the record check fails for a real lifted helper (`plain.rs:1015`), the
twin is built without that helper's plain `if`s. Then `f.unfold` shows
`Decidable.elim` where it would have shown `if`, with no warning and no
error. Records are exact now, so this should never happen. If it does,
it's a bug that's worth hearing about.

**Fix.** When a record exists and doesn't match,
`debug_assert!` (or panic under `CHECK_UNDOS`, as `cache/mod.rs:2650`
does), and keep the fallback in release builds. S.

### R4. The guard test can't fail for a leftover equation (low, high)

`a_call_in_a_guard_gets_the_equation` (`decreasing_twins.rs`) checks
only that the file loads without `W-DECREASING-UNFOLD`. It would also
pass if `f.unfold` kept `%found`'s equation for a guard-only call. Add a
`theorem countGuardUnfolds … := countGuard.unfold n k` stating the
`match` with no equation, as `countNestedUnfolds` does. S.

### R5. Comment and lookup in `twin()` (low, high)

- `plain.rs:1007-1010` says a rewind "could give the id to a definition
  that wasn't lifted", but the F7 check a few lines up already returns for
  any such definition. The remaining case is a stale `tables.lifted`
  entry (R2). The comment should say so.
- `twin()` searches the session-wide `tables.lifted` linearly once per
  helper (`plain.rs:996`), which is O(helpers × all lifted `match`es in
  the session). The old `lifted_at` did the same, but it now runs for
  every helper, before the body check. Search from the end (this
  declaration's entries are last), or build a set once in `plain_view`.
  S.

## Checked and sound

- F8, the lazy name check (`matching.rs:468`, `536-545`): `alias.is_none()`
  is tested first, so the check runs only when its result is used.
  `arms_call_itself` reads only the target and `alts`, which the loop
  doesn't change, so caching the result is exact.
- F6, exact records (`decreasing.rs:1466-1475`): the map is written
  every time a helper's body is set, and the record is removed when there
  are no tags. Records are never read across declarations (`Decl::rewind`
  drops `Active`).
- F7, twin spans: `lifted.push((made.twin, span))` is now unconditional,
  which is right since `span` always exists past the early return.
- F1's test asserts that no plain form keeps a dead non-`%` `let`, and
  the lane reports seeing it fail without the fix.
- F9 of SW-2208, the doc points on `arms_call_itself` and the module doc:
  both are fixed by this change.

## The 1 Nov review

`docs/research/rust-codebase-review.md` has no findings on these lines
(`plain.rs`, `arms_call_itself`, `lifted_helper_body`), so there's nothing
to update.

## Calls I made

- I rated R1 low, not medium: the orphan path needs a `with_local_retries`
  retry inside a `decreasing` body, the cost is dead definitions, and the
  failure is fail-soft.

## Tickets to file

One lane, Sonnet (near proof generation), about 45 min:

- R1: twins only of the final attempt's helpers (or of those reachable
  from the step's body).
- R2 and R3: a debug assertion in `rewind_globals`, and a loud fallback in
  checked builds.
- R4: a `countGuardUnfolds` theorem in `decreasing_twins.rs`.
- R5: the comment fix, and the lookup from the end.

Tests for the lane: `task test:one -- decreasing_twins`, plus the existing
`decreasing` proof tests it touches.

No D questions.
