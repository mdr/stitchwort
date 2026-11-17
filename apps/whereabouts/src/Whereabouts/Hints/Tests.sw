--| hints.test.ts's cases, and edge cases. A longitude band takes
--| `Math.cos(toRadians(lat))` as an input, so each answer here carries the
--| value Node gives for it. Expected bands are the TypeScript's own results.

namespace Whereabouts.Hints.Tests
import Whereabouts.Hints (..)
import Std (Float, List, Nat, Text)

--| An answer, with the cosine of its latitude.
type Place = { at: LatLon, cosLatitude: Float }

def place (lat lon cosLatitude: Float): Place := { at = { lat = { value = lat }, lon = { value = lon } }, cosLatitude }

def tajMahal: Place := place 27.1751 78.0421 0.8896149381042551

def fiji: Place := place (-17.7) 179.5 0.9526614812535863

def nearNorthPole: Place := place 89.0 0.0 0.017452406437283376

def london: Place := place 51.5 (-0.1) 0.6225146366376196

def sydney: Place := place (-33.8688) 151.2093 0.830315878062329

def bandOf (p: Place) (tolerance: Float) (axis: HintAxis) (unit: Float): HintBand :=
  hintBand p.at { value = tolerance } axis unit p.cosLatitude

def holds (p: Place) (tolerance: Float) (axis: HintAxis) (unit: Float): Bool :=
  inHintBand (bandOf p tolerance axis unit) p.at

def isBand (band: HintBand) (from to: Float): Bool := band.from.value == from ∧ band.to.value == to

test "always holds the answer, for either axis, wherever in the band it falls" :=
  [tajMahal, fiji, nearNorthPole, london, sydney].all (p =>
    [Latitude, Longitude].all (axis => [0.0, 0.37, 1.0].all (unit => holds p 150.0 axis unit)))

--| A band's width in kilometres, at 111.195 km a degree as the TypeScript test measures it.
def widthKm (band: HintBand): Float := (band.to.value - band.from.value) * 111.195

test "is about ten tolerances wide, and never puts the answer at an edge" := [0.0, 1.0].all (unit =>
  let band := bandOf tajMahal 150.0 Latitude unit
  let width := band.to.value - band.from.value
  Float.ieeeLe (10.0 * 150.0) (widthKm band)
    ∧ Float.ieeeLt (widthKm band) (10.0 * 150.0 + 2.0 * 111.195)
    ∧ Float.ieeeLt (0.1 * width) (27.1751 - band.from.value)
    ∧ Float.ieeeLt (0.1 * width) (band.to.value - 27.1751))

test "the Taj Mahal's bands are the TypeScript's" :=
  isBand (bandOf tajMahal 150.0 Latitude 0.0) 25.0 39.0
    ∧ isBand (bandOf tajMahal 150.0 Latitude 1.0) 15.0 30.0
    ∧ isBand (bandOf tajMahal 150.0 Longitude 0.37) 71.0 88.0

test "wraps a longitude band across 180°" :=
  let band := bandOf fiji 150.0 Longitude 0.5
  isBand band 172.0 (-173.0)
    ∧ Float.ieeeLt band.to.value band.from.value
    ∧ inHintBand band fiji.at
    ∧ ¬inHintBand band (place 0.0 0.0 1.0).at

test "stays inside the poles" :=
  let band := bandOf nearNorthPole 300.0 Latitude 1.0
  isBand band 63.0 90.0 ∧ inHintBand band nearNorthPole.at

test "rounds a narrow band to tenths of a degree" :=
  let band := bandOf london 10.0 Latitude 0.5
  Float.ieeeLt (band.to.value - band.from.value) 2.0 ∧ band.from.value * 10.0 == Float.round (band.from.value * 10.0)

test "describeHint names the edges with compass letters" :=
  describeHint { axis = Latitude, from = { value = 23.0 }, to = { value = 37.0 } } == "Between 23°N and 37°N"
    ∧ describeHint { axis = Latitude, from = { value = -5.5 }, to = { value = 4.0 } } == "Between 5.5°S and 4°N"
    ∧ describeHint { axis = Longitude, from = { value = 170.0 }, to = { value = -165.0 } } == "Between 170°E and 165°W"

test "describeHint leaves the letter off 0° and 180°, and off a -0" :=
  describeHint { axis = Longitude, from = { value = -0.0 }, to = { value = 180.0 } } == "Between 0° and 180°"
    ∧ describeHint { axis = Latitude, from = { value = -0.04 }, to = { value = 0.04 } } == "Between 0° and 0°"

-- Edge cases

test "a band near a pole is cut off at the pole, and a longitude band there at 120°" :=
  let polar := place 89.9 10.0 0.0017453283658982615
  let south := place (-89.95) 0.0 0.0008726645152351565
  isBand (bandOf polar 1000.0 Latitude 0.0) 0.0 90.0
    ∧ isBand (bandOf polar 1000.0 Longitude 0.5) (-50.0) 70.0
    ∧ isBand (bandOf south 50.0 Longitude 1.0) (-102.0) 18.0
    ∧ holds polar 1000.0 Latitude 0.0
    ∧ holds south 50.0 Longitude 1.0

test "a band across the antimeridian from the west" :=
  let dateLine := place 0.0 (-179.9) 1.0
  isBand (bandOf dateLine 150.0 Longitude 0.0) 178.0 (-168.0) ∧ holds dateLine 150.0 Longitude 0.0

test "unit 0 puts the answer nearer the band's low edge, and 1 nearer its high edge" :=
  let low := bandOf sydney 300.0 Latitude 0.0
  let high := bandOf sydney 300.0 Latitude 1.0
  Float.ieeeLt (-33.8688 - low.from.value) (low.to.value - -33.8688)
    ∧ Float.ieeeLt (high.to.value - -33.8688) (-33.8688 - high.from.value)
    ∧ Float.ieeeLt high.from.value low.from.value

test "a band just under 5° wide steps by tenths, and one just over by whole degrees" :=
  isBand (bandOf sydney 55.0 Latitude 0.5) (-36.4) (-31.3) ∧ isBand (bandOf sydney 56.0 Latitude 0.5) (-37.0) (-31.0)

--| The edges of a narrow longitude band go through `wrap`, which is exact
--| only for whole degrees: this band's `from` is 176.79999999999995, labelled
--| 176.8°E.
test "a narrow longitude band's edge is not its label" :=
  let band := bandOf (place 60.0 179.95 0.5000000000000001) 20.0 Longitude 1.0
  isBand band 176.79999999999995 (-179.5) ∧ describeHint band == "Between 176.8°E and 179.5°W"

test "seededUnit depends only on its inputs" :=
  seededUnit [1.0, 2.0, 3.0] == seededUnit [1.0, 2.0, 3.0] ∧ seededUnit [1.0, 2.0, 3.0] == 0.8164997166022658

test "seededUnit matches the TypeScript, whole parts taken modulo 2^32" :=
  seededUnit [] == 0.26642920868471265
    ∧ seededUnit [42.0, 0.0, 1.0] == 0.48845761083066463
    ∧ seededUnit [0.0] == 0.6442294681910425
    ∧ seededUnit [-1.0] == 0.4811337690334767
    ∧ seededUnit [4294967301.0] == seededUnit [5.0]
    ∧ seededUnit [5.0] == 0.5400921641848981

test "seededUnit spreads across 0 to 1" :=
  let values := List.range 0 200 |> .map (i => seededUnit [42.0, Float.ofNat i, 1.0])
  values.any (v => Float.ieeeLt v 0.1)
    ∧ values.any (v => Float.ieeeLt 0.9 v)
    ∧ values.all (v => Float.ieeeLe 0.0 v ∧ Float.ieeeLt v 1.0)
