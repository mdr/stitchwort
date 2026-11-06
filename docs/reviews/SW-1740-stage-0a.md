# SW-1740: stage 0a of bounded read-back, trip-journal on `lane/SW-1642`

Measurement only (docs/proposals/bounded-readback.md, stage 0a, D2544). Branch
`lane/SW-1740`, cut from `lane/SW-1642` (c91991954). Project:
`examples/projects/accept/trip-journal`, checked from inside its directory with
`stitchwort check` (the CLI takes no project path), a fresh copy with no `.stitchwort` cache.

Caveat for all timings: two other lanes were building on this machine, and some runs
ran two at once. Compare within a row of this note only. Node counts are exact; seconds are not.

## 1. What fails on the branch as it is

One error, then the three later namespaces are skipped (`E-NAMESPACE-FAILED`), so the
branch hides everything after it:

```
E-RESOURCE: a value was too large to show   Trip/Model.sw:163  type WellFormed
  Note 2: it happened while checking `WellFormed`
  Note 3: the value being shown was a call of `List.All`, computed far enough to be very large
```

**Site:** `Elaborator::accessors` (`shared.rs`, the accessor's type: the field's type read
back with `quote`, unfolded). Kind: **output term**. The blown-up field is one of
`WellFormed`'s `List.All (pin => pinFits trip.legs pin = True) trip.pins`-style fields
(`pinsFit`; inferred from the tally below, the accessor loop did not print the field).

**What unfolds:** the read-back unfolds `pinFits trip.legs pin` inside the `List.All`
predicate: `pinFits` -> `firstCovering` -> `Leg.covers` / `Leg.end` -> `Float` addition and
comparison on the symbolic `leg.start`, `leg.duration`, `pin.start`. A `Float` is a bit
pattern, so the unfolding is the bit-level formula (`Float.Model.signBit`, `magnitude`,
`Nat.sub`, `Nat.divFuel`, `Nat.mul`). Counts of definitions among the ~10,000,000 nodes
when it gave up: `Leg.duration` 894k, `Leg.start` 894k, `Nat.sub` 390k, `signBit` 314k,
`magnitude` 290k, `Nat.divFuel` 121k. The size limit is 10,000,000 nodes (`size_limit`);
nothing ran out of *work* first.

## 2. Every failing declaration, once the first failure is moved out of the way

Declaration by declaration is not possible on the branch (a namespace stops at the first
resource error). So I stood in for stage 1 with temporary switches (below): accessor types
and `decide` read back folded (`SW_ACC_FOLDED`, `SW_DECIDE_FOLDED`), rule 2 untouched. Then
`Trip.Model` checks, and `Trip.Proofs` shows **33 `E-RESOURCE` plus 1 `E-REWRITE-BUDGET`**;
`Trip.Merge` passes; `Trip.Tests` is skipped:

`remotePinsKept remotePinsKeptAsTheyWere stopIdsKept albumIdsKept atLeLastEnd legBounds
shiftPointsIds moveLegOk moveLegSame layoutSame keptFromCombined inCombined settleWithin
settleSelf keepsFits placePinFits placePinId placePinSelf resolveSelf mergeStopsSelf
mergePinsSelf albumEntriesSelf combinedSelf mergeAlbumsSelf mergeSelf mergeStopIds
mergePinIds albumEntryIds mergeAlbumIds settledAlbumsIds settledAlbumsOk mergePhotoIds
mergeAlbumsWithin` (33); the `E-REWRITE-BUDGET` is at `Placing.sw:22`.

Sites, by the innermost elaborator frame of each size-exceeded event (64 events; some are
swallowed by a caller, `ignorable_arguments` uses `.ok()?`, and each still cost a 10M-node
read-back; so events are not errors). Every event unfolds the same thing: `Float` arithmetic
on `Leg.start`/`Leg.duration` (and `Pin.startAt`, `Position.offset`, `Point.time`).

| Count | Site (frame) | Kind | Stage that moves it |
|---|---|---|---|
| 1 (branch as is) | `accessors` (`shared.rs`) | output term | 1 |
| 1 (+ 3 swallowed below) | `auto::decide` -> `cx.quote(prop)` (`WellFormed`'s derived `Decidable`, `undecidable_field`, field 4) | decide | 1 |
| 21 | `rewrite::rewrite_once` (via `rewrite_goal`) | search (find): the rule's left side looked for in the unfolded goal | 6a |
| 13 | `check::ignorable_arguments` (via `implicit_arg`, 3 under `decide_unglued`) | search (mentions) | 4 |
| 9 | `unify::both_forms` (via `zonk_changed`) | zonk | 4 |
| 8 | `matching::generalised_now` (5), `matching::blocker` (3), `check_match` (1) | search (match generalisation) | 6b |
| 10 | `Ctx::show_unfolded` (`alias_notes`), `first_difference_note`, `with_alike_updates_note`, `mismatch` | error note | 5 |
| 1 | `Comparison::blockers` | search (blockers of a comparison) | 6b / 4 (not studied) |
| 1 | `check_if_with` | other (an `if h:` condition, `List.Any`) | not studied |
| 1 | `rewrite::check_motive` | search (motive) | 6a |

Not measured: how many of the failing searches find their needle as written (needs a reader
that does not exist yet); whether `check.rs:378`/`substitute` is reached (no event had it in
its frames); the sizes of folded read-backs (not instrumented).

## 3. D2544's experiment: rule 2 off in the read-backs that searches use

Switch (`SW_ETA_OFF_SEARCH`, EXPERIMENT commits): `Ctx::quote`, the `quote` calls in
`cases.rs` and the accessor read-back go through `quote_search`, which makes `eta_case`
false while the read-back runs. Conversion and evaluation keep rule 2. Active only inside
namespaces named `Trip*`: switched on for all of std it breaks `Float.sw`'s own proofs
(`rewrite` finds no `Float.isNaN x`, `omega` fails), so rule 2 in searches is relied on
there.

Result, rule 2 off in searches only, no other change:

- `Trip.Model` **passes** (accessors and `decide` both): the first failure is gone.
  Adding the folded-`decide` stand-in changes nothing (same 62 events and the same errors),
  so with rule 2 off `decide` is not a failing site.
- `Trip.Merge` passes. `Trip.Proofs` fails with 12 `E-RESOURCE` (was 33), but 21
  `E-REWRITE-NOTHING`, 2 `E-REWRITE-MOTIVE` and 1 `E-REFL` appear that the stand-in run
  does not have: proofs that need rule 2 for `rewrite` to find its needle (`album.id`,
  `leg.id`, `mine.id`, `(merge local remote).legs`, `t < lo`, ...). `Trip.Tests` skipped.
  **Trip-journal does not pass.**
- Remaining resource sites after the experiment: zonk (`both_forms`, 11 events, limit 10,000
  nodes), error notes (`show_unfolded`, `mismatch` notes, `refl_error`, ~21), `ignorable_arguments`
  (14), `generalised_now`/`blocker` (9), `rewrite_once` (2).
- Rule 2 off everywhere in the namespace (`SW_ETA_ALL_OFF`, evaluation too) fails earlier,
  in `zonk_changed` at limit 10,000, still unfolding `Float` arithmetic. So the Float
  expansion is not only rule 2's: even without it, an unfolded read-back of a call with
  symbolic Float arguments is large. What rule 2 adds is the accessor and `decide` cases.
  (Why `main` is fine on this project is not established here: it also lacks the SW-1667
  commits; I did not bisect.)

Invalid first attempt: I first scoped the switch by a flag that was reset by nested std
elaboration, so the first "identical numbers" runs were switch-off no-ops; only the runs
from the fixed scope (A, B in the timings) are used above.

## 4. Timings (wall clock, noisy)

| Run | Wall | Result |
|---|---|---|
| `main` binary, cold cache | 7.9 s (user 3.9 s) | passes; 0.2 s cached |
| branch as is, cold | 10.4 s | fails at `WellFormed`, rest skipped |
| branch + stage-1 stand-ins (`SW_ACC_FOLDED`, `SW_DECIDE_FOLDED`) | 4:01 | 33 + 1 errors; user 216 s |
| branch + experiment (`SW_ETA_OFF_SEARCH`), two runs at once | 6:16 | 12 + 21 + 2 + 1 errors; user 240 s |

Nearly all of the minutes are failed 10,000,000-node read-backs (62 to 64 events at
roughly 3 to 4 s each), on the error paths. A passing run would not pay these. The speed
goal (at most twice `main`'s time) cannot be judged until the failures move.

## 5. What it means for the stage plan

- **Stage 1 (output terms and `decide`) is needed and moves the first failure:** the
  branch's one visible error, `accessors`, plus `decide`. It is not sufficient: with both
  stood in for, `Trip.Proofs` still has 33 resource failures.
- **D2544's experiment is not enough on its own, and costs proofs.** It removes the
  accessor and `decide` failures (so it could replace stage 1 on the branch for trip-journal,
  but stage 1 is wanted on `main` anyway) and cuts the resource failures from 33 to 12,
  while breaking about 24 proofs that rely on rule 2 inside `rewrite`. Not adopted.
- **What trip-journal needs before SW-1667 resumes**, by kind of the remaining sites:
  stage 1, then 4 (mentions, zonk: `ignorable_arguments` and `both_forms` appear in both
  runs), 5 (error notes; ~10 events, and in the experiment run they are the majority of what
  remains), 6a and 6b (`rewrite_once`, `generalised_now`, `blocker`: 29 events in the first
  run). These sites do not fail only on the error path: `rewrite_once` and `generalised_now`
  are search failures in proofs, so 6a and 6b, and with them R and M, are on the path. The
  earliest honest "SW-1667 resumes" point is therefore after 6b, not after stage 1.
- **Worth trying first, cheaply:** the unfolded read-back of `Float` addition and comparison
  on symbolic operands is what everything unfolds. A hold on `Float` operations in the
  unfolded read-back (`Float.add`, `Float.leq` stay calls when an argument is stuck, as
  `matches_at_once` already keeps them folded) would plausibly shrink every site at once,
  including the ones above that stage 1 does not touch. Not tried; it is a design question
  for the note (a limit that fails does not help here, since the proofs need the answer).

## Reproducing

The switches are in the two EXPERIMENT commits on `lane/SW-1740` (never merge them):
`SW_ETA_OFF_SEARCH`, `SW_ETA_ALL_OFF`, `SW_ACC_FOLDED`, `SW_DECIDE_FOLDED`; all active only
in namespaces named `Trip*`. The backtrace and tally instrumentation (an `eprintln!` at the
size-limit point in `value.rs::quote_as`, a per-definition tally of visited calls) is not
committed. Build: `nix develop -c cargo build --release -p stitchwort-cli`; run from a copy of
the project directory with `.stitchwort` removed.
