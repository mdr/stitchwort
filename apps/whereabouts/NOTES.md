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

Proved (`stitchwort audit Whereabouts.Hints.Proofs`: 21 theorems, 0 failed,
0 with warnings):

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
  180 → -180, -180 → -180), and `tenthsKeepTheirLabel`: `describeHint`'s
  rounding, `Math.round(d * 10) / 10`, leaves each of the 3,601 tenths from
  -180° to 180° as it is. So the label of an edge that *is* a tenth is that
  edge; finding 2 is that longitude edges aren't tenths.
- `floatLeTrans`, `floatLeLtTrans`: transitivity of the total order, for
  the above (std has it only inside `Ord`; see "std gaps").

Not proved, with the law each needs. Each holds only for finite inputs in
range (|lat| ≤ 90, -180 ≤ lon < 180, 0 ≤ unit ≤ 1, 0 < width ≤ 120 for
longitude); "the answer is in its band" also needs the tolerance bound from
finding 1.

| Theorem | Laws it needs (stage 3 or 4) |
|---|---|
| margin before rounding: the answer is at least 0.15 · width from each unrounded edge | `placeAt 0 = 0.15` and `placeAt 1 = 0.85` compute; it needs `*` and `+` monotone (done, SW-3843: `Float.mulMonotoneLeft` and `Float.mulMonotone` for a non-negative finite factor, `Float.addMonotoneLeft` and `Float.addMonotone`, all for finite operands), and an error bound on `lat - at * width` against the exact value (the standard model, `|fl(a ∘ b) − (a ∘ b)| ≤ 2^-53 · |a ∘ b|` for `∘` in `+ - * /` without overflow). The real-number statement is not quite the float one: with rounding the margin is 0.15 · width minus a few ulps. |
| outward rounding contains the unrounded band, step 1 | Done (`outwardRoundingWhole`, SW-3830), for edges below 2^49 in size. |
| outward rounding, step 0.1 | false as stated (finding 1). True form: `floorTo x 0.1 <= x + 2^-45` for `|x| ≤ 360` (and `ceilTo` symmetric), which needs the error bounds of `/` and `*`, `floor`'s spec, and `round` within ½ of its argument. |
| the answer is in its band | the step 0.1 row (wide bands need only step 1, done) and the margin row; `Float.min`/`Float.max` laws for non-NaN operands (done, SW-3843: `Float.minLeLeft`, `minLeRight`, `minEither`, `leMin`, `max`'s likewise, and `minIeeeLeLeft` and so on in JS's order); latitude's clamps (`Float.max (-90.0) _`, `Float.min 90.0 _`) keep an answer with `|lat| ≤ 90`; the bridge from the total order to JS's comparison, which `inHintBand` uses (done, SW-3843: `Float.ieeeLeOfLe`, and back `Float.leOfIeeeLe`, which allows two zeros; `Float.ieeeLtOfLt` and `Float.ltOfIeeeLt` for `<`); the tolerance's lower bound from finding 1; and for longitude, that `wrap` of a whole-degree edge is the edge shifted by an exact multiple of 360 (sums of whole numbers below 2^53 are exact, `Float.Theory.addWhole`, and `rem` is exact), and the wrapped-interval reading of `inHintBand` (`from > to` means `[from, 180) ∪ [-180, to]`) against the unwrapped band. |
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

Missing laws: see the table. In short, stage 3 and 4's customer here wants,
in order of how much they unlock: monotonicity of `*` (`/` and `ofNat` are
done, SW-639); `+`
monotone on the left for finite operands; the standard-model error bound;
`floor`/`ceil`/`round` specs (`floor x <= x` and `x <= ceil x` are done;
whole, within 1); `rem`'s range and exactness; Sterbenz.

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
(counterexamples as theorems, 3,601 tenths checked in well under a second);
and the extracted JS matched the TypeScript bit for bit first time.
