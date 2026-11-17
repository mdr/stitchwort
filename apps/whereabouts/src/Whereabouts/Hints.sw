--| Hints: a band of latitude or longitude the answer lies in, ported from
--| Whereabouts' `packages/shared/src/hints.ts`, bit for bit. A band narrows
--| one direction only, so a player still has to know where along it to look.

namespace Whereabouts.Hints

import Std (Float, Int, List, Nat, Text)

--| Kilometres, on the ground.
@[js.unboxed]
type Km = { value: Float }

@[js.unboxed]
type Degrees = { value: Float }

type LatLon = { lat: Degrees, lon: Degrees }

@[js.enum]
type HintAxis =
  | @[js.name "LATITUDE"] Latitude
  | @[js.name "LONGITUDE"] Longitude

--| A longitude band that crosses 180° has `from` greater than `to`.
type HintBand = { axis: HintAxis, from: Degrees, to: Degrees }

--| A band's width, in the round's tolerances.
def hintWidthTolerances: Float := 10.0

--| The answer is never in this outer share of the band at either edge.
def edge: Float := 0.15

--| A longitude band near a pole would otherwise span most of the world.
def maxLongitudeSpan: Float := 120.0

def earthRadius: Float := 6371.0

--| JS's `Math.PI`.
def pi: Float := 3.141592653589793

--| Degrees of arc along a great circle that span `km` on the ground.
def kmToDegrees (km: Float): Float := km / ((earthRadius * pi) / 180.0)

def toRadians (degrees: Float): Float := (degrees * pi) / 180.0

--| JS's `Math.min` of two: the NaN if either is, and `-0` below `0`, which
--| the total order already gives.
def jsMin (a b: Float): Float :=
  if Float.isNaN a ∨ Float.isNaN b then Float.nan
  else if a <= b then a
  else b

--| JS's `Math.max` of two.
def jsMax (a b: Float): Float :=
  if Float.isNaN a ∨ Float.isNaN b then Float.nan
  else if a <= b then b
  else a

def floorTo (value step: Float): Float := Float.round (Float.floor (value / step) * step * 10.0) / 10.0

def ceilTo (value step: Float): Float := Float.round (Float.ceil (value / step) * step * 10.0) / 10.0

--| Longitude into [−180, 180): JS's `%` truncates, so it is applied twice.
def wrap (lon: Float): Float := (((lon + 180.0) % 360.0 + 360.0) % 360.0) - 180.0

--| Where the answer sits across the band, from `unit` (0 to 1): never in the
--| outer `edge` at either side.
def placeAt (unit: Float): Float := edge + unit * (1.0 - 2.0 * edge)

--| Edges are rounded outwards to tenths of a degree in a band under 5°, else to whole degrees.
def stepFor (width: Float): Float := if Float.ieeeLt width 5.0 then 0.1 else 1.0

--| The latitude band `width` wide (at most 180°) around `lat`, with `lat` at `at` across it.
def latitudeBand (lat width at: Float): HintBand :=
  let unclamped := lat - at * width
  let from := jsMin (jsMax unclamped (-90.0)) (90.0 - width)
  let step := stepFor width
  {
    axis = Latitude,
    from = { value = jsMax (-90.0) (floorTo from step) },
    to = { value = jsMin 90.0 (ceilTo (from + width) step) }
  }

--| The longitude band `width` wide around `lon`, with `lon` at `at` across it.
def longitudeBand (lon width at: Float): HintBand :=
  let from := lon - at * width
  let step := stepFor width
  { axis = Longitude, from = { value = wrap (floorTo from step) }, to = { value = wrap (ceilTo (from + width) step) } }

--| The band of `axis` around `answer`, with the answer at a point set by
--| `unit` (0 to 1) away from the edges. Edges are rounded outwards to whole
--| degrees, or tenths for a narrow band, so the labels are the band.
--|
--| `cosLatitude` is `Math.cos(toRadians(answer.lat))`, which the caller
--| supplies until std has `cos` (D3675); only a longitude band uses it.
export def hintBand (answer: LatLon) (tolerance: Km) (axis: HintAxis) (unit cosLatitude: Float): HintBand :=
  let span := kmToDegrees (hintWidthTolerances * tolerance.value)
  let at := placeAt unit
  match axis with
    | Latitude => latitudeBand answer.lat.value (jsMin span 180.0) at
    | Longitude => longitudeBand answer.lon.value (jsMin (span / cosLatitude) maxLongitudeSpan) at

--| Whether a point lies in the band, edges included, by JS's comparisons.
export def inHintBand (band: HintBand) (point: LatLon): Bool :=
  let from := band.from.value
  let to := band.to.value
  match band.axis with
    | Latitude => Float.ieeeLe from point.lat.value ∧ Float.ieeeLe point.lat.value to
    | Longitude =>
      if Float.ieeeLe from to then Float.ieeeLe from point.lon.value ∧ Float.ieeeLe point.lon.value to
      else Float.ieeeLe from point.lon.value ∨ Float.ieeeLe point.lon.value to

--| An edge to the tenth, with its compass letter: `23°N`; `0°` and `180°` have none.
def describeEdge (positive negative: Text) (degrees: Float): Text :=
  let magnitude := Float.abs (Float.round (degrees * 10.0) / 10.0)
  if Float.ieeeEq magnitude 0.0 ∨ Float.ieeeEq magnitude 180.0 then "${magnitude}°"
  else "${magnitude}°${if Float.ieeeLt 0.0 degrees then positive else negative}"

--| "Between 23°N and 37°N", "Between 170°E and 165°W".
export def describeHint (band: HintBand): Text :=
  let describe := match band.axis with
    | Latitude => describeEdge "N" "S"
    | Longitude => describeEdge "E" "W"
  "Between ${describe band.from.value} and ${describe band.to.value}"

-- seededUnit: mulberry32 over 32-bit words, each a `Nat` below 2^32.

def wordSize: Nat := 4294967296

--| JS's `ToUint32`, which `^`, `|`, `Math.imul` and `>>>` apply to a
--| `number`: its whole part modulo 2^32 (0 for the NaN and the infinities).
def toWord (x: Float): Nat := match Float.toInt (Float.trunc x) with
  | Some i => Int.toNat (Int.mod i (OfNat wordSize))
  | None => 0

--| JS's `Math.imul`, on words: the product modulo 2^32.
def imul (a b: Nat): Nat := a * b % wordSize

--| The mixed state before the last step, a word: the parts folded in, then
--| two rounds of mulberry32's mixing.
def mix (parts: List Float): Nat :=
  let folded := parts.foldLeft 1831565813 (hash part => imul (Nat.xor hash (toWord part)) 2654435761)
  let first := imul (Nat.xor folded (Nat.shiftRight folded 15)) (Nat.or folded 1)
  Nat.xor first ((first + imul (Nat.xor first (Nat.shiftRight first 7)) (Nat.or first 61)) % wordSize)

--| The word `seededUnit` divides by 2^32.
def finalWord (parts: List Float): Nat :=
  let state := mix parts
  Nat.xor state (Nat.shiftRight state 14) % wordSize

--| A number from 0 to 1 that depends only on its inputs (mulberry32).
export def seededUnit (parts: List Float): Float := Float.ofNat (finalWord parts) / 4294967296.0
