# Whereabouts pilot 1: hint bands (SW-3790)

A port of Whereabouts' `packages/shared/src/hints.ts` (`hintBand`,
`inHintBand`, `describeHint`, `seededUnit`, `floorTo`, `ceilTo`, `wrap`) to
`Whereabouts.Hints`, to find Stitchwort's gaps on real shipped float code
(D3674). `trimToHint` and `cellMeetsBand` are left out: they need H3.

- `src/Whereabouts/Hints.sw`: the port.
- `src/Whereabouts/Hints/Tests.sw`: hints.test.ts's cases (the catalogue
  loop replaced by five places), and edge cases: a pole, the antimeridian
  from both sides, `unit` 0 and 1, bands just under and just over 5° wide.
- `src/Whereabouts/Hints/Proofs.sw`: what is proved, and what is settled by
  computing.

## Bit for bit

`stitchwort build --js Whereabouts.Hints` gives a `.d.ts` whose shapes are
the TypeScript's (`HintAxis = "LATITUDE" | "LONGITUDE"`, `Degrees = number`,
`HintBand = { axis, from, to }`), except two: `hintBand` takes one more
argument, `cosLatitude` (`Math.cos(toRadians(lat))`, until std has `cos`,
D3675), and `seededUnit` takes an array instead of rest parameters.

Compared under Node with the TypeScript's own functions on 100,000 random
inputs (latitudes and longitudes on, near and off tenths; tolerances from 0
to 5,000 km; `unit` 0, 1, 0.5 and random; seeds with negatives, fractions,
NaN, ±Infinity, -0 and 2^60): `hintBand`'s edges (`Object.is`),
`inHintBand`, `describeHint` and `seededUnit` agreed every time.

- `Math.round` is `Float.round` exactly (half towards +∞, sign of zero kept).
- JS `%` is `Float.rem` exactly (truncating, the dividend's sign).
- JS `<`, `<=`, `>=` are `Float.ieeeLt` / `Float.ieeeLe`, not `<` and `<=`,
  which are the total order: `-0.0 <= 0.0` but not `0.0 <= -0.0`.
- `Math.min` and `Math.max` of two are `Float.min` and `Float.max` (the NaN
  wins, and `-0` is below `0`); `Ord.min` would let the NaN lose.
- mulberry32 is modelled as words: `Nat`s below 2^32, `Math.imul` as the
  product mod 2^32, `^`, `|`, `>>>` as `Nat.xor`, `Nat.or`, `Nat.shiftRight`,
  and the signed `state + Math.imul(…)` as a sum mod 2^32 (ToInt32 of the sum
  has the same bits). A part goes in through JS's ToUint32 (`toWord`).

## What the port found in hints.ts

1. **Outward rounding can pull an edge past the answer**, when the band is
   narrower than the rounding error. Proved by computing
   (`narrowLatitudeBandMissesAnswer`): at a tolerance of 1e-13 km, the
   answer -87.60000000000001 gets the band [-87.6, -87.5] and is outside it,
   because `-87.60000000000001 / 0.1` rounds to exactly -876, so `floorTo`
   rounds *up*. On longitude `wrap` adds its own error, and the largest
   failing tolerance found in a random search was 2.6e-12 km
   (`narrowLongitudeBandMissesAnswer`). Real tolerances are kilometres, so
   this never happens in a game, but it means the containment theorem needs
   a lower bound on the tolerance (about 1e-11 km is enough: the margin,
   0.15 of the width, has to beat about 6e-14°). Breaking `floorTo` to
   round down a little further makes both theorems fail.
2. **A narrow longitude band's edges aren't its label.** `wrap` is exact on
   whole degrees but not on tenths: `wrap 0.1 = 0.10000000000002274`
   (`wrapTenth`). Of the tenths from -300° to 300°, 4,176 of 6,001 come out of
   `wrap` as another double. So a band shown as "Between 176.8°E and 179.5°W"
   starts at 176.79999999999995 (test "a narrow longitude band's edge is not
   its label"), and a point exactly on a labelled edge can be outside the
   band. A fix to try in hints.ts: wrap `from` before rounding it, so that
   `floorTo`'s tenths are the edges, and map a rounded 180 to -180 (exact).
3. `wrap` of NaN or ±Infinity is NaN; nothing upstream can produce one, but
   the theorem `wrap` ∈ [-180, 180) needs a finite input.

## Theorems

Proved (`stitchwort audit Whereabouts.Hints.Proofs`: 143 theorems, 0
failed, 17 with warnings, SW-3872: the random tests found no inputs meeting
the hypotheses of 17 arithmetic helpers stated over 2^1074-sized units or
exact integer relations, each used with its hypotheses proved, so none is
vacuous). Checking takes about 11 s without the cache, 8.5 s of it std's
own check; nothing is settled by a computed table any more (SW-3872 and
SW-3807 replaced the three, which had taken it to 2.7 minutes):

- `finalWordBelow`: mulberry32's last word is below 2^32. Unconditional.
- `seededUnitInUnit` (via `wordUnitInUnit`): `0.0 <= seededUnit parts ∧
  seededUnit parts < 1.0`. Unconditional since float laws stage 4 (SW-639):
  std's `Float.ofNatMonotone` and `Float.divMonotone` (division by a
  positive finite double), and the largest word divides to
  0.99999999976716936 < 1, and 0 to 0.0.
- `wrapRange`: `-180.0 <= wrap lon ∧ wrap lon < 180.0` for every finite
  `lon` (SW-3805). `lon + 180.0` is finite (below the overflow threshold);
  `% 360.0` leaves it below 360 in size (std's `Float.Theory.remUnits`);
  `+ 360.0` makes it non-negative (`Float.Theory.addAtLeast`), so the second
  `% 360.0` is non-negative (`Float.remNonneg`) and below 360, hence at most
  359.99999999999994, the double below; then `- 180.0` rounds between -180
  and 179.99999999999994 (`addAtLeast`, `addAtMost`). Sterbenz isn't needed:
  the bound by the double below 360 does the work.
- `outwardRoundingWhole` (SW-3830): for `|from|, |to| < 2^49`,
  `floorTo from 1.0 <= from ∧ to <= ceilTo to 1.0`, so rounding to whole
  degrees never moves an edge inwards. It follows from `floorToWhole`
  (`floorTo x 1.0 = Float.floor x`) and `ceilToWhole` (`ceilTo x 1.0 =
  Float.ceil x`), zero signs included, with std's `Float.floorLe` and
  `Float.ceilGe`. Those two use std's `Float.divOneRight` (`x / 1.0 = x`),
  `Float.mulOneRight`, and `Float.roundTenthsOfFloor` / `roundTenthsOfCeil`
  (`round (floor x * 10.0) / 10.0 = floor x` for `|x| < 2^49`), built on
  `Float.Theory.mulTenWhole` and `divTenWhole` (`* 10.0` and `/ 10.0` exact
  on whole numbers of either sign, via `roundWholeUnits`). The order is the
  total one: `ceilTo (-0.5) 1.0` is `-0.0`, which is above -0.5 either way.
- By computing: `narrowLatitudeBandMissesAnswer`,
  `narrowLongitudeBandMissesAnswer`, `wrapTenth`, `wrapWhole` (23 → 23,
  180 → -180, -180 → -180).
- `tenthsKeepTheirLabel` (SW-3807): `describeHint`'s rounding,
  `Math.round(d * 10) / 10`, leaves every tenth up to 360.1° in size as it
  is: `round (tenth r * 10.0) / 10.0 = tenth r` for `|r| ≤ 3601`. So the
  label of an edge that *is* a tenth is that edge; finding 2 is that
  longitude edges aren't tenths. By the standard model (`labelRound`):
  `/ 10.0` and `* 10.0` each miss by at most 2^-53 of the value, far inside
  the half unit `round` allows. (It was a computed list of the 3,601 tenths
  from -180° to 180°; the checker evaluates a closed `List.all` statement
  even when the proof is general, so the law took its quantified form.)
- `floatLeTrans`, `floatLeLtTrans`: transitivity of the total order, for
  the above (std has it only inside `Ord`; see "std gaps").
- Latitude's clamps (SW-3844): `latitudeClampRange` (`Float.max (-90.0)
  (Float.min 90.0 y)` is in [-90, 90] for every `y` but the NaN), and the
  two the band uses: `clampFromKeeps` (clamping a lower edge at -90 keeps
  it at most an answer with `-90 <= lat`) and `clampToKeeps` (likewise the
  upper edge at 90).
- The margin row, in its monotone form (SW-3844): `placeAtRange` (`0.15 <=
  placeAt unit <= 0.85` for `0 <= unit <= 1`, rounding included) and
  `marginRow`: `lat - 0.85 * width <= lat - placeAt unit * width <= lat -
  0.15 * width` for finite `lat`, finite non-negative `width`, every
  operation rounded as the code rounds it. With std's new
  `Float.subAntitoneRight`, `Float.finiteBetween`, `Float.mulCommFinite`
  and `Float.zeroMulNonneg`.
- By computing (SW-3844): `floorToTenthOneUlpAbove` and
  `ceilToTenthOneUlpBelow`, the counterexamples to the earlier step-0.1
  bound (see the table).
- Outward rounding to tenths (SW-3858, SW-3872). `tenthsAt` proves, for
  each whole number `k` of tenths from -3601 to 3601: the round trip
  `round (k * 0.1 * 10.0) = k` (`tripNonzero`: `Float.mulRelError` twice,
  then `Float.roundNear`), and that the doubles 3 · 2^-44 below and above
  its tenth divide by 0.1 to below and above `k` (`slackBelow`,
  `slackAbove`: `Float.divRelError` for `k / 10.0`, `slackSum` for the
  shift, `divRelError` again for `/ 0.1`; the errors come to about 27.5 of
  the 30 · 2^-44 the slack moves it, at `|k| = 3601`). From it:
  `tenthsRoundTrip` (the round trip for every whole double up to 3601,
  both zeros included), `floorToTenth` and `ceilToTenth` (`floorTo x 0.1 =
  floor (x / 0.1) / 10.0` for `|x| ≤ 360`, likewise `ceil`), and the
  step-0.1 bounds `floorToTenthBound` (`floorTo x 0.1 ≤ x + 2^-42`) and
  `ceilToTenthBound` (`x ≤ ceilTo x 0.1 + 2^-42`), for `|x| ≤ 360` in exact
  units of 2^-1074. The argument: if `x` were below the double `c` 3 ·
  2^-44 under `floorTo x 0.1`, `x / 0.1 ≤ c / 0.1 < k ≤ x / 0.1`
  (`Float.divMonotone`, `Float.floorLe`); and `c` is within 2^-44 of its
  exact value (`slackSum`, from `Float.addRelError`). SW-3858 did the
  per-`k` work with a computed table of 7,203 rows (2 minutes of
  checking); SW-3872 replaced it with the general proof above, with the
  same statements and the same 2^-42 bound.
- The margin, exactly (SW-3858). `marginBelowExact`: for `|lat| ≤ 361`,
  `0 ≤ unit ≤ 1` and a width from 1e-11° to 361°, the unrounded lower
  edge is at least 2^-42 below the answer in exact units:
  `units (lat - placeAt unit * width) + 2^1032 ≤ units lat`.
  `marginAboveExact`: for `|lat| ≤ 180` and a width from 1e-11° to 180°,
  the unrounded upper edge `from + width` is at least 2^-42 above it. With
  `sumNear` (a rounded sum within 361° is within 2^-43 of the exact one,
  by `Float.addRelError` with the sign cases), `shareAbove` (`0.85 *
  width` is at least 8 · 2^-44 below `width`, by `Float.mulRelError`) and
  `unitsNeg` (`units (-x) = -units x`, a std candidate). A width of 1e-11° is a tolerance of about 1.1e-10 km (10 tolerances wide,
  111 km a degree on latitude); finding 1's counterexamples are at 1e-13 and
  2.6e-12 km.
- Longitude on whole degrees (SW-3858): `wrapWholeExact`: `wrap` of a
  whole number `n` of degrees, `|n| ≤ 400`, is exactly `wrappedDegrees n`
  (`(n + 180) mod 360 - 180`, `n` shifted by a multiple of 360 into
  [-180, 180)). Every step is exact on whole numbers (SW-3872, replacing
  a table of the 801 values): the sums by `addWholeExact`, the remainders
  by `remWholeStep` from `remUnitsExact` (`x % y` is `x` less a whole
  number of `y`s, with `x`'s sign, which std's `remExact` proves inside
  but doesn't state), and `wrapArith` for the integers' side.

Not proved, with the law each needs. Each holds only for finite inputs in
range (|lat| ≤ 90, -180 ≤ lon < 180, 0 ≤ unit ≤ 1, 0 < width ≤ 120 for
longitude); "the answer is in its band" also needs the tolerance bound from
finding 1.

| Theorem | Laws it needs (stage 3 or 4) |
|---|---|
| margin before rounding: the answer is at least 0.15 · width from each unrounded edge | Done (SW-3858): `marginBelowExact` and `marginAboveExact`, at least 2^-42 in exact units for a width of at least 1e-11° (the float form, `marginRow`, SW-3844, is what they start from). |
| outward rounding contains the unrounded band, step 1 | Done (`outwardRoundingWhole`, SW-3830), for edges below 2^49 in size. |
| outward rounding, step 0.1 | false as stated (finding 1), and the bound `floorTo x 0.1 <= x + 2^-45` given here before is false too (SW-3844, `floorToTenthOneUlpAbove`: from 256° an ulp is 2^-44). Done in its true form (SW-3858): `floorToTenthBound` and `ceilToTenthBound`, 2^-42 for `\|x\| ≤ 360` in exact units, with the round trip (`tenthsRoundTrip`) on the way. A search of 800,000 inputs found the error at most one ulp (2^-44 at most within 360°), so 2^-42 has room to spare. |
| the answer is in its band | Not assembled yet (SW-3858 stopped here); every part below is proved. Done: step 1 (`outwardRoundingWhole`) and step 0.1 (`floorToTenthBound`, `ceilToTenthBound`); the exact margin (`marginBelowExact`, `marginAboveExact`), which carries finding 1's tolerance bound as `1e-11 <= width`; the `Float.min`/`Float.max` laws (SW-3843); latitude's clamps (SW-3844); the bridge to JS's comparison (`Float.ieeeLeOfLe`, SW-3843); `wrap` on whole degrees (`wrapWholeExact`). Left: (1) latitude: the clamps move `from` towards the answer, or to -90 itself, where `floorTo (-90.0) 0.1` is exactly -90 (by computing), and likewise `from + width` at 90, though the clamped `from + width` needs its own margin (when `unclamped < -90`, `-90 + width` against `lat`); chaining the unit bounds into `<=` (`Float.Theory.lessOfUnits`, `unitsMonoKey`) and then `ieeeLeOfLe`; and the width's lower bound from the tolerance's, through `kmToDegrees` and `Float.min span 180.0`. (2) longitude: a narrow band rounds to tenths, and `wrap` is not exact on tenths (finding 2), so its containment needs `wrap`'s error on a tenth (a few ulps, by `addRelError` and `remUnits`) inside the margin, or finding 2's fix in hints.ts; a wide band needs `wrapWholeExact` and the wrapped-interval reading of `inHintBand` (`from > to` means `[from, 180) ∪ [-180, to]`) against the unwrapped band, split by whether the band crosses ±180; and `span / cosLatitude`, which needs a bound on the caller's cosine. |
| `wrap` ∈ [-180, 180) for finite input | Done (`wrapRange`, SW-3805). It used: `rem`'s range: `y > 0` finite, `x` finite → `|x % y| < y`, sign of `x`, exact (`x − n·y` for the whole `n` of truncated division); `+ 360.0` of a value in (-360, 360) lands in [0, 720] (rounding may reach 720, which `% 360` maps to 0); Sterbenz for `z - 180.0` with `z` in [90, 360) (exact), and `z - 180.0 < 180.0` for `z < 360` below 90 by monotonicity. |
| `describeHint` names the edges | nothing about `Float.toText` can be proved (only the runtimes compute it). What can be stated is `tenthsKeepTheirLabel` (done), and for every input, that latitude edges are tenths: `round` returns a whole double (`Float.toInt (round x) = Some k`), and `/ 10.0` of a whole double is `tenth k`. Longitude edges aren't (finding 2). |

## Friction

What was awkward to express:

- **JS comparisons have no operators.** `point.lat >= band.from` is
  `Float.ieeeLe band.from point.lat.value`; `width < 5` is `Float.ieeeLt
  width 5.0`. `<=` exists but is the total order, which is wrong at `0.0`
  vs `-0.0`, and nothing warns when a port uses it. Reading the code back
  against the TypeScript is slow: every comparison is flipped into prefix
  form. A JS-order operator (or a `Float.Js` namespace with `<.`, `<=.`)
  would make ports read like their source.
- **Units as unboxed records have no arithmetic.** `Degrees` and `Km` are
  `@[js.unboxed]` records, as the brief asked, and cross as `number`
  (good), but inside they need `.value` everywhere, so the code unwraps at
  the boundary and works on bare `Float`s, losing the units exactly where
  the TypeScript keeps them (its flavours allow `+` and `*`). A way to
  derive or lift `Float`'s operations onto a one-field record would close
  this.
- **No `cos`** (known, D3675): `hintBand` takes `cosLatitude`, and every
  longitude test carries a cosine copied from Node.
- **mulberry32 needed a hand-written word model**: no `UInt32`/`Word32`, no
  `imul`, no ToInt32/ToUint32 in std. `toWord` goes `Float.trunc` →
  `Float.toInt` → `Int.mod` → `Int.toNat`. A std module of JS's 32-bit
  number operations would make every hash and PRNG port a one-liner.
- There are no rest parameters, so `seededUnit(...parts)` became
  `seededUnit(parts)`: the TypeScript callers would need `[ ]` around their
  arguments.

Missing laws: see the table. Monotonicity, the standard-model error bound
(SW-3844), `round`'s spec (SW-3844), `rem`'s range and Sterbenz are done;
the step-0.1 chain and the exact margin use them (SW-3858). What is left is
assembling the containment theorem (the table's last rows). std candidates
from SW-3858: `unitsNeg` (`units (-x) = -units x` for non-NaN `x`), and
`sumNear`'s two-sided form of `Float.addRelError` with the sign handled. From SW-3872: `remUnitsExact` (the exact value of `x % y`),
`addWholeExact` (`Float.Theory.addWhole` with the sum's finiteness), and
`relCancel` (the error model's bounds with the common unit cancelled).

Other std gaps:

- `Math.min`/`Math.max` (`Float.min`/`max` are listed as later in
  float.md).
- Transitivity of `<=`/`<` on `Float` as named theorems
  (`Float.leTrans`, `Float.leLtTrans`): they exist only as `Ord`'s `trans`
  on `compare`, so the proofs here prove them again through `orderKey` and
  `arithmetic`.

Error messages that misled:

- `parts.foldLeft (hash part => …) 1831565813`, with the arguments in the
  wrong order, said "this is a function, but the expected type is `_`".
  The expected type is the accumulator's; the message could name the
  parameter (`initial`) or suggest swapping.
- `let word := finalWord parts` then `arithmetic [finalWordBelow parts]` in
  a proof was `E-RESOURCE` ("a value was too large to write out … a call of
  `Nat.sub`"), on the theorem's whole header: the checker had unfolded
  mulberry32 on an unknown list. Stating the lemma for any `word` fixed it.
  The note didn't say which step did it; the line of the `let` would have
  saved a bisection.
- `byComputing` on `a = b ∧ c = d` says it "proves an equation"; it could
  suggest the tuple `(byComputing, byComputing)`.

What went well: `stitchwort test` runs `describeHint`'s text tests at run
time even though the checker can't compute `Float.toText`; `byComputing`
settles real questions about a whole program on known doubles
(counterexamples as theorems);
and the extracted JS matched the TypeScript bit for bit first time.
