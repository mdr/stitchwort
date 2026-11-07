# SW-2219: a review of the trip-journal example project

*7 November 2026, Opus, read-only, against `main` at `b3ced2d59`. The
project is `examples/projects/accept/trip-journal` (SW-996, 1 Nov): 1,558
lines in `src/Trip/Model.sw`, `Merge.sw`, `Tests.sw` and `Proofs/*.sw`. I
read all of it, the README, SW-996, SW-999, SW-1015, SW-1016 and SW-1744's
report, the proving guide, `docs/proposals/std-naming.md` and the record-eta
notes. I ran the main checkout's release binary on the project (`check`,
`test`, `audit Trip`, `search`, `doc`) and on a scratch copy of it in the
session scratchpad, to try changes and probe the merge with extra tests.
Nothing in the repo was edited except this file.*

## Summary

**Verdict: worth keeping and worth a refresh, and two bugs in the model
need fixing first.** The project reads well. The Float handling is careful
and right: a position keeps the old time, so a leg that doesn't move gives
its items back bit for bit. `-0.0`, the NaN and the infinities are ruled
out for the right reasons. `mergeWellFormed` covers all twelve fields of
`WellFormed`, and `mergeSelf` is a real theorem. As a regression test it has
already paid for itself: SW-1744 traced record eta's Float blowup through
it, and nothing else in the corpus caught that.

But the theorems miss the property a sync merge most needs, and two probes
against it found real bugs in the model, both on well-formed trips:

- **A planned stop can end up linked to a different place.** Stops point
  at places by *index* (`Planned (index: Nat)`), and merging the same plan
  renumbers its places. A stop planned at the local "fort" is linked to the
  remote "mill" after the merge.
- **A pin that both copies have can be lost.** The remote position wins.
  If that position no longer fits the merged leg, the pin is dropped, even
  when the local position would fit. On the next sync it comes back from
  the device that still has it.

Neither breaks a stated theorem: `WellFormed` doesn't relate planned stops
to the plan, and `remotePinsKept` keeps only what `placePin` keeps. What
users of a merge care about is that syncing again changes nothing:
`merge l (merge l r) = merge l r`. That law fails here only because of the
pin bug. It holds for all 121 pairs of the 11 well-formed fixtures I
tried, so it is the headline theorem to add.

On standards, the code predates record eta, D2422's implicit parameters
and the house call-site style. About 200 of its 1,558 lines would go
without changing a statement's meaning: 40 from record eta, 10 from std's
`List.decSorted`, and 60 to 90 from naming the merge's entry lists in
`Merge.sw` rather than restating them in the proofs. Most of the rest of
the style work makes lines shorter rather than fewer.

**Top five recommendations**

1. **Fix the two model bugs** (F1, F2): link planned stops by place id,
   with a `WellFormed` field saying the place is in the plan, and let a pin
   fall back to the other copy's position. Sonnet, 90 min.
2. **Prove that syncing again changes nothing**: `mergeAbsorbs: WellFormed
   l → WellFormed r → merge l (merge l r) = merge l r` (F3). After 1. This
   is the theorem the example exists to show. Opus, 90 min.
3. **Refresh for current standards** (F6 to F9): record eta, `<=` and `<`,
   `.id`, implicit parameters, dot calls, the named entry lists in
   `Merge.sw`. Two Sonnet lanes, one after the other.
4. **Fill in the "nothing lost" set** (F4, F5): local legs and pins kept,
   the kept leg has the most points, the plan's places kept, a stop inside
   its own leg (the README already claims that one), well-formed fixtures
   with a `byDecision` theorem each. Sonnet, 60 min.
5. **Answer SW-996's open item with order, not distance** (F10). That an
   item lands within an ulp of its old offset needs a relative-error law.
   That items in a moved leg *keep their order* needs only that `+` and `-`
   are monotone on finite doubles, and std's rounding lemmas
   (`roundsToMono`, `roundKeyMono`) are most of that proof. Opus, 90 min.

**Counts:** 0 high, 4 medium, 8 low.

## Findings

| # | Where | Finding | Sev | Conf | Size |
|---|---|---|---|---|---|
| F1 | `Model.sw:30-32`, `Merge.sw:179-184` | Planned stops link to places by index; merging the same plan renumbers places, so a local stop is relinked to another place (repro below) | medium | high | M |
| F2 | `Merge.sw:121-136` | A pin both copies have is dropped when the remote position doesn't fit the merged leg, though the local one would; it reappears on the next merge (repro below) | medium | high | M |
| F3 | `Proofs/` | No convergence theorem. `merge l (merge l r) = merge l r` is the law a sync needs; it fails only through F2 on the fixtures | medium | high | M (Opus) |
| F4 | `Proofs/Kept.sw:16-21` | `remotePinsKept` assumes `placePin … = Some placed`, the merge's own helper, so it says little more than "`filterMap` keeps what it keeps". No theorem for local legs or local pins at all | medium | high | S-M |
| F5 | `README.md:94-96`, `Proofs/Placing.sw:28-48` | The README says stops and albums are proved "inside the leg"; `settleWithin` proves only inside the trip | low | high | S |
| F6 | `Proofs/Self.sw:10-37`, `:197-218`, `Placing.sw:79-80` | Record eta makes `albumEta`, `tripEta`, `rebuildTrip`, `Album.rebuilt` and the three `startAtSame` lemmas `rfl`, and `mergeSelf` one `rewrite`; the comment "there is no eta rule for records" is now false | low | high | S |
| F7 | `Model.sw:124-151` | `decSorted` and `decPinsSorted` duplicate std's `List.decSorted`, which the derived decision finds; the comment says std has none | low | high | S |
| F8 | throughout | Call-site style: `Float.leq a b` for `a <= b` (40 sites), `leg => leg.id` for `.id` (about 115), `List.map xs f` prefix forms in statements, `Nat.leq (n + 1) m`, `not (a == b)`, `Text.isEmpty (Text.trim t)`, `clamp lo hi t` with two unnamed Floats, free functions that read as methods (`holds album id`, `unlink stop`) | low | high | M |
| F9 | `Proofs/*.sw` (68 sites) | The proofs restate the merge's entry lists (`local.stops.map (stop => ((if replaced then unlink stop else stop), locate local.legs stop.start))`) instead of naming them once in `Merge.sw`; `stopEntries`, `pinEntries`, `albumEntries` live in `Proofs/WellFormed.sw` with `…Is := rfl` lemmas tying them back | low | high | M |
| F10 | `README.md:83-96` | SW-996's open item. Order within a moved leg is provable with monotonicity alone, so it needn't wait for a relative-error law | low | medium | M (Opus) |
| F11 | `Merge.sw:76-77`, `Model.sw:81` | `clamp` puts a stop past its shortened leg at `leg.end`, but a leg covers `start <= t < end`, so the stop then belongs to the *next* leg on every later sync (confirmed: `locate` gives leg 3) | low | high | S-M |
| F12 | `Tests.sw` | 4 of the 13 fixtures are not well-formed (unsorted pins: `localPin`, `movedPin`, `extraPin`; a pin past its leg: `shortened`), so those scenarios run the merge outside the proved domain; only `base` has a `WellFormed` theorem | low | high | S |

The 14 audit warnings are not findings against the project: §4 explains
them, and the tooling side is SW-1261 and SW-1317, plus D3221 below.

## 1. Is it sensible?

### The model

Yes, as a picture of two-device merging, with three gaps a reader should be
told about:

- **Nothing is ever deleted.** Every id of either copy survives
  (`stopIdsKept`, `albumIdsKept`, and local legs by construction). A stop
  deleted on one device comes back from the other. This is the classic
  reason for tombstones, and it's fine to leave out of a small example,
  but the README should say so under "Not modelled".
- **The merge isn't symmetric, so a protocol is implied.** `merge r (merge
  l r)` differs from `merge l r` for 110 of 225 fixture pairs (stops come
  local-first, pins remote-first). That's correct if one device merges and
  both adopt the result, which the README should state; F3's law is then
  exactly what that protocol needs.
- **The policies differ by item, without a stated reason.** Stops and albums
  take the local position; pins take the remote one. If that's deliberate,
  to show both, the README should say so.

The "more track points wins" rule for a leg drops the other copy's points
whole. That is stated, and it's a plausible crash-recovery rule.

### F1. Planned stops are linked by index

`StopKind.Planned (index: Nat)` points into `itinerary.places`.
`mergeItinerary` keeps the same plan as "the remote places, then the new
local ones", so a place added locally moves to a later index whenever the
remote device also added one. `WellFormed` has no field linking a planned
stop to the plan, so neither theorem notices. Repro, added to a scratch
copy of `Tests.sw` (it passes, and `fortStop` is well-formed by
`byDecision`):

```
def fortStop: Trip := { withPlace base { id = 3, name = "fort" } | stops = base.stops ++ [{ id = 5, start = 800.0, name = "fort", kind = Planned 2 }] }
-- placeName looks the stop's place up by its index
test "a planned stop changes place" :=
  placeName fortStop 5 == Some "fort" ∧ placeName (merge fortStop (withPlace base { id = 4, name = "mill" })) 5 == Some "mill"
```

**Fix:** `Planned (placeId: Nat)`, and a `WellFormed` field: every planned
stop names a place in the itinerary. `mergeWellFormed` then needs that
field. When the plan was replaced, the stops are unlinked. When it's the
same plan, every local place is kept (`keyMemAppendNewByRight`), and a
remote stop's place is in the remote list. The one-sided case, where the
remote copy has no plan and keeps the local one, needs remote planned
stops to have a place, which the remote copy's `WellFormed` gives (no
plan, so no planned stops).

### F2. A pin both copies have can be lost

`mergePins` keeps, for a shared id, only the remote entry
(`appendNewBy fromRemote fromLocal`), and `placePin` drops a pin whose
position doesn't fit. When the merged leg is the *local* one (more points)
and shorter than the remote leg, a remote pin late in the remote leg is
dropped, even though the local copy of the same pin fits. Repro (passes;
`localDense` is well-formed by `byDecision`, and `base` already is):

```
def denseFerry: Leg := { ferry | duration = 500.0, points = [{ id = 3, time = 600.0 }, { id = 4, time = 900.0 }, { id = 6, time = 1000.0 }] }
def localDense: Trip := {
  base |
  legs = [walk, denseFerry],
  pins = [{ id = 1, start = 50.0, duration = 30.0 }, { id = 2, start = 700.0, duration = 100.0 }],
  summary = Some (summarize [walk, denseFerry])
}
test "a pin both copies have is dropped, and comes back on the next merge" :=
  let m := merge localDense base
  (m.pins.map (pin => pin.id)) == [1] ∧ ((merge localDense m).pins.map (pin => pin.id)) == [1, 2]
```

**Fix:** keep both positions for a shared pin, and place it from the
remote one if that fits, else from the local one. The theorem then becomes
"a pin of either copy is kept if either of its positions fits the merged
legs" (F4). It also makes F3 provable.

### F3. The missing headline: syncing again changes nothing

`mergeSelf` covers syncing two identical copies. The real case is a device
that syncs, adopts the result `m`, then syncs again with a server that
already has `m`: `merge l m` should be `m`. I checked
`merge l (merge l r) == merge l r` as a test over all pairs of the 11
well-formed fixtures (`Tests.sw`'s, plus two three-leg trips of mine) and
`localDense`: 144 pairs. It fails for 8 of them, all with `localDense` as
`l`, through F2. (`merge (merge l r) (merge l r) = merge l
r` holds on all 225 pairs of the 15 fixtures, as `mergeSelf` and
`mergeWellFormed` predict.) The
proof can reuse `mergeSelf`'s machinery: `settleSelf`, `placePinSelf`, and
the fact that the merged legs already contain the local ones. Ownership of
photos is the risky part. State it, run the counterexample search, and
expect a day's surprise in `owner`.

### F4. What else "nothing lost" should say

- `localLegsKept`: every local leg id is in the merge (the mirror of
  `remoteLegsKept`; `memAppendNewBy` gives it).
- Pins, after F2: a pin of either copy is kept when it fits, stated with
  `Pin.fitsIn` and the merged leg rather than with `placePin`.
- `keptLegMostPoints`: a merged leg has at least as many points as the leg
  with its id in each copy. That is the leg rule's promise.
- `placesKept`: with the same plan, every place of either copy is in the
  merged plan.
- `settleInLeg` (F5): a stop or album whose position names a leg of the
  merged legs lands in that leg's `start .. end`. It follows from
  `clampLow` and `clampHigh` in a few lines, and makes the README true.

### F10. Where an item lands in a moved leg

The README is right that a distance bound needs a relative-error law.
What a user notices is order: photos in a leg shouldn't swap. "If `t1 <=
t2` in the old leg, their new times are in the same order" needs `x <= y
→ s + x <= s + y` and the same for `-`, on finite doubles (with an infinity
or NaN it fails: `+inf + -inf` is NaN, above `+inf + +inf` in the total
order). Std has only `Float.addMonotoneRight` (`s <= s + d` for `0.0 <=
d`), but `Float.Theory` has the monotone rounding lemmas that the general
law is built from. Clamping is monotone too, so order is kept even when an
item is clamped. That would turn the "Not proved" section into a sharper
statement.

### F11. A clamped stop changes legs

`settle` clamps into `leg.start .. leg.end`, inclusive at the end.
`Leg.covers` is half-open, so `leg.end` is the next leg's start. With legs
walk, ferry and bus, and the ferry shortened on the remote copy, a local
stop at 1400 lands at 1100, and `locate` puts 1100 in the bus (checked in
the scratch copy). Its time doesn't change on the next sync. But it now
moves with the bus, and is relinked if the legs are reordered or a
local-only leg is placed after the ferry. Fix: clamp to the last double
below `end`, which needs a `Float.nextDown` (bits minus one for a positive
finite double, and not in std), or clamp to `start`, which keeps the leg
but loses the position. A small decision for the fixing lane. Low.

## 2. Is it up to current standards?

| Rule | State | Notes |
|---|---|---|
| Domain records with methods | mostly | Good records throughout (`Leg`, `Pin`, `Position`, `Summary`), with `Leg.end`, `Leg.covers`, `Pin.fitsIn` and `Photo.id`. Free functions that read as methods: `holds album id` → `album.holds id`, `unlink stop` → `stop.unlink`, `keepOwned own album`, `withPhotosOf remote album` → `album.withPhotosOf remote`, `placeIn leg pos` → `leg.place pos`. The merge's entries are `(Stop, Position)` pairs read with `.fst`/`.snd` (68 times in proofs); a `Placed a = { item: a, at: Position }` record reads better (F9). The list-of-legs functions (`lastEnd`, `firstCovering`, `findLeg`, `within`) want a home; a `Route` record would give one, but it isn't worth it before F9 |
| Named numeric and bool arguments | no | `clamp leg.start leg.end (placeIn leg pos)` (two Floats; better `leg.clamp t`, or `clamp (low := …) (high := …) t`), `shiftNotes from to notes` (two Floats) |
| Dots and pipes | partly | `List.sortWith placed byStart` → `placed.sortWith byStart`; `(albums.find …).map (album => album.id)` → `albums.find … \|>.map .id`; `Text.isEmpty (Text.trim text)` → `text.trim.isEmpty`; statements use `List.map xs f` and `List.Distinct (…)` prefix forms, which could be `(trip.legs.map .id).Distinct`; I checked that this form elaborates to the same proposition (`rfl`) |
| Operators | partly | Propositions use `∧`, `∨`, `∈`, `∉`, `=`. Code says `Float.leq a b` and `Float.less a b` 40 times where `a <= b` and `a < b` are the same functions (I checked `rfl` against `Leg.covers`); `Nat.leq (remote.points.length + 1) local.points.length` is `remote.points.length < local.points.length`; `not (a == b)` is `a != b` |
| `.toSet`/`.toMap` | n/a | no sets or maps |
| Clause lambdas | n/a now | Clause definitions are used where they fit (`Photo.id`, `planReplaced`, `mergeItinerary`); the entry lambdas would become clause lambdas over pairs, but the record of F9 is better |
| Brackets, ability rows | yes | `[x, ..xs]` throughout (D2324 sweep); no abilities |
| Comments | mostly | Fresh-reader comments, with the why. Stale: `Self.sw:10` ("there is no eta rule for records"), `Model.sw:124` ("nothing in std decides" covers `Sorted`, which std now decides); the README's "inside the leg" (F5) |
| Proving guide: implicit parameters (D2422) | no | The local lemmas take every argument explicitly: `findLegMem legs id leg h`, `placePinFits legs pin pos kept h`, `keepsFits`, `legOfMem`, `holdsMem`, `floatLeTrans x y z h1 h2` (all fixed by the hypothesis). `floatLeTrans`, `floatLeRefl` and `floatLessLe` are one-line aliases of `Ord.leTrans`, `Ord.leRefl` and `Ord.lessLe`; call those |
| Proving guide: spec apart from program | partly | `WellFormed` is a spec in the problem's words; `remotePinsKept` is stated through `placePin` (F4) |
| Proving guide: break the program once | not recorded | SW-996 doesn't say it was done; F1 and F2 suggest a mutation run with the new theorems |

## 3. Features since 1 November, and lines each would save

Measured on a scratch copy where I could (the changes checked); estimated
otherwise.

| Feature | Applies? | Lines |
|---|---|---|
| Record eta | Yes. I checked that `Album.rebuilt`/`albumEta`, `rebuildTrip`/`tripEta`, `stopStartAtSame`, `albumStartAtSame`, `pinStartAtSame` and `keepOwnedSelf`'s last step are all `rfl` now, and that `mergeSelf` is one `rewrite … in rfl` without its 22-line `calc`. `moveLegSame` still needs its split on `notes` (`Option.map` of an identity) | −40 |
| Fields of calls | Already relied on (`(merge l r).legs` computes); nothing to change | 0 |
| `decreasing` without names | No `decreasing` definitions; all recursion is structural | 0 |
| `match found:` and its transport | The proofs already name their equations (`match e: …`); the transport could drop a few `rewrite … in` steps in `placePinSelf` and `settleSelf`, not worth its own lane | 0 to −5 |
| Maps of sets | No maps; photo ownership is a function, which suits the proofs | 0 |
| Std lemmas from AoC (SW-2138, SW-2169) | None of them is duplicated here. Searched: `ifSame` (no std form), `decAll` (none), `albumsOk` (std has `distinctFlatMap` the other way only), `firstCoveringMem`/`findLegMem` (wrappers of `List.findSome`). The one duplicate is older: `decSorted` and `decPinsSorted`, which std's `List.decSorted` replaces. I checked that `byDecision` still proves `WellFormed base` without them | −10 |
| `Ord` aliases | `floatLeTrans`, `floatLeRefl`, `floatLessLe` | −9 |
| `List.unique` and std-naming.md | No `List.distinct` calls. The §1.5 renames reach 19 sites here (`List.memMap` 18 → `memMapIntro`, `List.memFilter` 1 → `memFilterElim`), which N5's sweep should cover; no line change | 0 |
| Implicit parameters (D2422) | Local lemmas and their ~40 call sites | −15 (rewrapped lines) |
| Named entry lists in `Merge.sw` (F9) | 68 restated lambdas in the proofs, and the `…Is := rfl` lemmas | −60 to −90 |

The project would go from 1,558 lines to about 1,350-1,400 before F1-F5's
additions put some back.

Two std candidates fell out: `ifSame` (`(if c then x else x) = x`; by
std-naming's rule 7 it is `Bool.ifSelf`) and a `Decidable (List.All p xs)`
from a decision for `p`. The second would remove five of the six
hand-written instances in `Model.sw` and the workaround the comment
describes. Std should have both. They're small enough to go with the
next std lane rather than a lane of their own.

## 4. The 14 audit warnings

Every warning is "no input made the hypotheses true (0 of 1500)". None of
them is a narrow hypothesis in the proving guide's sense: each set of
hypotheses is satisfiable, and most have a witness in the project already.
Random generation just can't build the inputs.

| Theorem | Hypotheses | Why random inputs miss | Satisfiable? |
|---|---|---|---|
| `Trip.Model.pinFits.eq.some`, `Trip.Merge.keepsIn.eq.some` | `firstCovering legs pin.start = Some leg` | a random `Float` start inside a random leg, *and* `leg` equal to the one found | yes; generated equations, true by construction (SW-1261 option A) |
| `Trip.Merge.placePin.eq.some.ifTrue`, `.ifFalse` | `legOf legs pos = Some leg` and `keepsIn … = b` | `pos.leg` must name a leg of `legs` and `leg` equal it | yes; generated (SW-1261) |
| `Trip.Merge.owner.eq.ifTrue`, `.ifFalse.ifTrue` | `stillHolds merged id (holder local id) = True` | an album id that exists and holds a photo id that also exists | yes; generated (SW-1261) |
| `placePinFits`, `placePinId`, `remotePinsKept` | `placePin legs pin pos = Some kept` | as above, plus `kept` equal to the result | yes: `Tests.extendedPinKept` witnesses `remotePinsKept` |
| `remotePinsKeptAsTheyWere` | `WellFormed remote`, merged legs = `remote.legs`, `pin ∈ remote.pins` | a well-formed trip with a pin needs a leg covering it, and `pin` must be one of its pins | yes: `base`, `base`, pin 1 (not yet a theorem in `Tests.sw`) |
| `holderOf`, `ownerSelf` | distinct photo ids, `album ∈ albums`, `photo ∈ album.photos` | membership of an independently generated record | yes: `base.albums`, album 1, `Plain 1` |
| `inCombined` | distinct remote album ids, `id` a photo id of either copy | two random `Trip`s with a photo, and `id` matching it | yes: `base`, `base`, 1 |
| `photoIdsKept` | `WellFormed remote`, `id` a photo id | a well-formed trip with an album needs `0.0 <= start <= lastEnd`; with no legs `start` must be exactly `0.0` | yes: `base`, `base`, 1 |

SW-996's report said "4 narrow-hypothesis warnings (each witnessed in
Tests)". The count rose to 14 when generated equations started being
audited and when the derived decision for `WellFormed` let the search try
theorems it used to skip.

**What to do.** In the project, nothing is wrong. Add one-line witness
theorems in `Tests.sw` for the six without one (as `extendedPinKept`
does), so a reader sees that each set of hypotheses holds. That goes in
the F4/F12 lane.

In the tool, six warnings are SW-1261's (generated equations: skip them,
since they come from the definition) and the rest are SW-1317's shape
(hypotheses that equations or membership determine). There is also a
cheaper, non-random answer to D2357's doubt. A theorem that some checked
declaration applies to closed arguments, with every hypothesis given, has
satisfiable hypotheses. That's proved, not sampled. The audit could print
"witnessed by `Trip.Tests.extendedPinKept`" and not warn. D3221.

## 5. What it's for

**As a test, yes, it pulls its weight.** `the_trip_journal_checks` is the
corpus's one sizeable proof over `Float` sums of unknowns under binders
(`leg.start + leg.duration` inside `List.All` predicates). That is the
shape that blew up on the record eta branch (SW-1744, D2551). The
three `float-*` files in `examples/accept` don't have it. It checks in
about 4 s and tests in 0.5 s. The refresh lanes below keep that shape:
`WellFormed`'s fields and `Leg.end` stay as they are. After the refresh,
check that the test still fails on SW-1744's prototype commit, or at
least that `check` takes about as long. A refresh that made it cheaper
would make it a weaker regression test.

**As a guide piece, not yet, and not as a tour page.** The tour pages are
a few dozen lines each, and this is 1,500. Two parts would teach well
after F1-F3:

- A tour page on **doubles in proofs**: why `placeIn` keeps the old time,
  with the two rounding tests (`0.9` coming back as `0.8999999999999999`
  if recomputed) and `placeUnmoved`. About 40 lines, and a newcomer would
  enjoy it.
- A guide case study, **"proving a sync merge"**: `WellFormed`, the merge,
  `mergeWellFormed`, and `mergeAbsorbs` as the payoff. That's a later
  decision, once F3 is proved.

## Checked and sound

- `mergeWellFormed` provides every `WellFormed` field from the right
  lemma. Stops and albums are within the trip for any position
  (`settleWithin`), pins fit by construction, and pins are sorted by
  `sortWithSorted` with `Float.leTotal`.
- `mergeSelf` needs exactly `WellFormed`'s fields: `legIds`, `contiguous`,
  `stopsWithin`, `pinsFit`, `pinsSorted`, `albumIds`, `photoIdsDistinct`
  and `albumsWithin`. Its statement is bit-for-bit equality, because
  `Float`'s `==` is `DecEq` on bits (`DecEq.refl` rewrites it).
- The `GoodDuration` explanation in the README is right: `-0.0 < 0.0` in
  the total order, NaN and `+inf` are above `0.0`, and finiteness isn't
  used by any proof.
- `summaryMatches` and `mergeSummaryFresh` say what the README says.
- `placeUnmoved` and the two rounding tests are right, and are the best
  part of the project as an explanation of doubles.
- `check` (4 namespaces, 4 s), `test` (19 of 19) and `audit Trip` (187
  theorems, 0 failed, 14 warnings, §4) all match the brief.
- `merge (merge l r) (merge l r) = merge l r` held on all 225 fixture
  pairs, well-formed or not.

**The 1 Nov codebase review** (`docs/research/rust-codebase-review.md`)
covers the Rust crates; it has no findings about this project.

## Calls I made

- I put F1 and F2 at medium, not high. They are wrong answers, but in an
  example project, and no stated theorem is false.
- I didn't recommend a `Route` record for the list-of-legs functions. It
  would touch most of the proofs, for less gain than F9.
- I didn't recommend a lane for `match found:` transport or
  `decreasing`: nothing here gains enough.
- I left the order of the lanes to the orchestrator, except where one
  needs another (below).

## D questions

- **D3220:** fix the model's two bugs (F1, F2) and make "syncing again
  changes nothing" the project's headline theorem (F3), knowing that this
  changes what the example does, not just how it reads? [rec: yes. The
  example exists to show conflict resolution, and these are the bugs such
  a merge must not have. The Float-under-binders shape that makes it a
  regression test is untouched.]
- **D3221:** should the audit treat a theorem as witnessed, with no
  vacuity warning, when a checked declaration applies it to closed
  arguments with all its hypotheses (as `Tests.extendedPinKept` does)?
  This is a proved, non-random check, an answer to D2357's doubt about
  random search. [rec: yes, as a short design note first (Opus, 45 min),
  alongside SW-1261.]

## Tickets to file

In order; L1 and L2 touch the same files, so they run one after the other.
Each lane's tests: the project's `check`, `test` and `audit Trip`, plus
`task test:one -- the_trip_journal_checks` and `hash_stability::projects`.

1. **L1 [Sonnet] Trip journal: model fixes**: planned stops by place id,
   with a `WellFormed` field; pins fall back to the other copy's position;
   F1's and F2's repros as tests; `mergeWellFormed` and `mergeSelf`
   updated. Optionally F11 (the clamp's end), with the choice recorded.
   After D3220. 90 min.
2. **L2 [Sonnet] Trip journal: current style, part 1**: F6 (eta `rfl`s,
   short `mergeSelf`), F7 (drop `decSorted`, `decPinsSorted`), the stale
   comments, F8's operators (`<=`, `<`, `!=`, `.id`, dot calls, named
   `clamp` arguments), D2422 implicit parameters on the local lemmas, and
   `Ord` instead of the `float*` aliases. Statements keep their meaning
   (orchestrator checks each, D2436). After L1. 60 min.
3. **L3 [Sonnet] Trip journal: current style, part 2**: F9. Name the entry
   lists in `Merge.sw` with a `Placed` record, make `holds`, `unlink`,
   `keepOwned`, `withPhotosOf` and `placeIn` methods, and drop the proofs'
   restated lambdas and `…Is` lemmas. After L2. 75 min.
4. **L4 [Sonnet] Trip journal: what is kept**: F4 and F5 (`localLegsKept`,
   pins of either copy, `keptLegMostPoints`, `placesKept`, `settleInLeg`)
   and the README updated; F12 (sort the fixtures' pins, a `byDecision`
   `WellFormed` theorem for each fixture, a witness theorem for each §4
   warning without one); the README's "Not modelled" (deletion, the
   adopt-the-result protocol, why stops and pins differ). After L1. 60 min.
5. **L5 [Opus] Trip journal: syncing again changes nothing**: F3,
   `mergeAbsorbs`. Run the counterexample search on the statement first.
   After L1 (and best after L3, whose names shorten it). 90 min.
6. **L6 [Opus] Std: `+` and `-` monotone on finite doubles, and order in a
   moved leg**: F10. `Float.addMonotone` and `Float.subMonotone` (finite
   arguments) from `Float.Theory`'s rounding lemmas, then the trip theorem
   that items in a moved leg keep their order. Std lemmas need snap:hashes
   and `hash_stability`. 90 min.
7. **Small, with the next std lane [Sonnet]:** `Bool.ifSelf` (now
   `Trip.Proofs.ifSame`) and a `Decidable (List.All p xs)` from a decision
   for `p`, then delete the local copies. 30 min.
8. **D3221's design note [Opus]**, if yes: witnessed theorems in the
   audit. 45 min.
9. **Later, not now:** a tour page "doubles in proofs" from `placeIn` and
   its two tests, after L1 to L3.
