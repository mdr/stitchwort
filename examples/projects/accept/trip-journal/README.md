# Trip journal: merging two offline copies, with Float times

A trip journal kept on two devices, each edited offline, and `merge local
remote`, which combines the two copies. Times are `Float` seconds from the
start of the trip, and the proofs are about those doubles as they are,
rounding included. It is a test-corpus project (`examples/projects/accept`):
`cargo test` checks it and runs its tests.

## The parts

| Namespace | File | What |
|---|---|---|
| `Trip.Model` | `src/Trip/Model.sw` | The journal, and `WellFormed` |
| `Trip.Merge` | `src/Trip/Merge.sw` | `merge local remote` |
| `Trip.Proofs` | `src/Trip/Proofs/*.sw` | The theorems below |
| `Trip.Tests` | `src/Trip/Tests.sw` | Worked scenarios, and `WellFormed` of an example trip |

A trip has GPS legs laid end to end from 0 (each with track points and
optional route notes), stops (free, or linked to a planned place), photo pins
(a span of time), albums of photos, an optional itinerary (a file id and its
places), an optional auto-generated summary, a name and settings.

## The merge

1. **Legs**, by id: a leg in both copies keeps the one with more track points
   (the remote one on a tie), with the remote route notes if it has them,
   else the local ones, moved to the kept leg's start. Remote legs come
   first, then the local-only ones, all laid end to end from 0 again; a leg
   that moves takes its points and notes with it.
2. **Things pinned to a time** keep their place in the leg they were in. A
   position records the leg's id, the offset into it, and the leg's start and
   the time itself, so an item in a leg that didn't move gets back exactly its
   old time. Stops and albums take the local position and are clamped into
   their leg (with no leg, into the trip); pins take the remote position, are
   dropped if they no longer lie wholly inside their leg, and are sorted by
   start.
3. **Albums** in both copies have the remote photos, then the new local ones.
   A photo then in several albums stays in the album that held it in the local
   copy, if that album still holds it, else the remote copy's, else the first.
4. **A replaced itinerary** (the remote one has another file id) frees the
   local stops linked to the old plan. The same plan merges its places.
5. **The summary** is kept only with the legs it was made from: the remote
   one if the remote legs are the merged legs, else the local one if the local
   legs are, else none.
6. **The name** is the remote one unless it's blank; the settings are the
   remote copy's.

## What is proved

`WellFormed trip` (Model.sw): legs contiguous from `0.0` (each starts at the
previous start plus its duration, exactly), distinct leg ids, distinct track
point ids in each leg, durations finite and `0.0 <= d` in the total order,
distinct pin ids, each pin wholly inside the first leg covering its start (a
leg covers `start <= t < end`), pins sorted by start, distinct stop and
album ids, photo ids distinct across all albums, stops and albums within
`0.0 .. end of the last leg` (`0.0` with no legs), distinct planned-place
ids.

`-0.0` is not a good duration: it is below `0.0` in the total order. Adding
it would change nothing (`Float.addNegZero`), but the proofs use std's
`Float.addMonotoneRight`, which needs `0.0 <= d`. The NaN and `+infinity`
satisfy `0.0 <= d` in the total order, so finiteness rules them out; no proof
needs it, since in the total order they are just large.

- `mergeWellFormed`: two well-formed copies merge to a well-formed trip.
- `mergeSelf`: a well-formed trip merged with itself is unchanged, to the
  bit.
- Nothing important is lost: `remoteLegsKept` (every remote leg id),
  `remotePinsKept` (every remote pin that still fits its leg after the merge),
  `remotePinsKeptAsTheyWere` (all of them, unmoved, when the merged legs are
  the remote ones), `stopIdsKept` and `albumIdsKept` (either copy's),
  `photoIdsKept` (every photo of either copy is in some merged album, and by
  `mergeWellFormed` only one), `summaryMatches` (a merged summary is a copy's
  whose legs are exactly the merged legs) and `mergeSummaryFresh` (so a
  summary made from its copy's legs is made from the merged legs).
- `placeUnmoved`: in a leg that didn't move, a position gives back its exact
  time.

## Not proved

- **Offsets in a moved leg.** A stop in a leg that moved goes to the new
  start plus its old offset, and `(start' + (t - start)) - start'` need not
  be `t - start` in doubles: the test "a moved leg can round the offset"
  shows `0.3`, `0.2` into a leg at `0.1`, ending up `0.19999999999999996`
  into the leg moved to `0.5`. A theorem bounding that error would need a
  relative-error law for `+` and `-` (|round(x) - x| <= 2^-53 |x| for normal
  results), which std's `Float.Theory` has the pieces for (its rounding
  specification) but doesn't state. So nothing is proved about where in a
  moved leg an item lands, beyond it being inside the leg (stops, albums,
  kept pins) and inside the trip.
- **Which pins are dropped.** The proofs say that every pin kept fits, and
  every remote pin that fits after the merge is kept; that a pin is kept
  whenever its leg merely grew is not proved (it depends on the rounding
  above).
