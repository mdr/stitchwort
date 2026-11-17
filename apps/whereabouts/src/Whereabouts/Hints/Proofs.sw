--| What is proved about hint bands, and what is settled by computing.
--| std's float laws (std/Float/Theory.sw) cover `seededUnit`; NOTES.md
--| lists the laws the other band theorems still need.

namespace Whereabouts.Hints.Proofs
import Whereabouts.Hints (..)
import Std (Bool, Eq, Float, Int, List, Nat)

--| mulberry32's last word is a word.
theorem finalWordBelow ∀ (parts: List Float): finalWord parts < 4294967296 :=
  Nat.modLt (Nat.xor (mix parts) (Nat.shiftRight (mix parts) 14)) 4294967296

theorem floatLeTrans ∀ (x y z: Float) (xy: x <= y) (yz: y <= z): x <= z :=
  let a: Int.leq (Float.orderKey x) (Float.orderKey y) = True := xy
  let b: Int.leq (Float.orderKey y) (Float.orderKey z) = True := yz
  (arithmetic: Int.leq (Float.orderKey x) (Float.orderKey z) = True)

theorem floatLeLtTrans ∀ (x y z: Float) (xy: x <= y) (yz: y < z): x < z :=
  let a: Int.leq (Float.orderKey x) (Float.orderKey y) = True := xy
  let b: Int.less (Float.orderKey y) (Float.orderKey z) = True := yz
  (arithmetic: Int.less (Float.orderKey x) (Float.orderKey z) = True)

--| `seededUnit` is in [0, 1): `ofNat` and division by a positive finite
--| double are monotone, and the largest word, 2^32 - 1, divides to
--| 0.99999999976716936, below 1.
theorem wordUnitInUnit ∀ (word: Nat)
    (word32: word < 4294967296):
    0.0 <= Float.ofNat word / 4294967296.0 ∧ Float.ofNat word / 4294967296.0 < 1.0 :=
  let below: word ≤ 4294967295 := arithmetic
  let positive: 0.0 < 4294967296.0 := byComputing
  let finite: Float.isFinite 4294967296.0 = True := byComputing
  let atLeastZero: Float.ofNat 0 / 4294967296.0 <= Float.ofNat word / 4294967296.0 :=
    Float.divMonotone
      (Float.ofNat 0)
      (Float.ofNat word)
      4294967296.0
      positive
      finite
      (Float.ofNatMonotone 0 word (arithmetic))
  let atMostTop: Float.ofNat word / 4294967296.0 <= Float.ofNat 4294967295 / 4294967296.0 :=
    Float.divMonotone
      (Float.ofNat word)
      (Float.ofNat 4294967295)
      4294967296.0
      positive
      finite
      (Float.ofNatMonotone word 4294967295 below)
  let zero: Float.ofNat 0 / 4294967296.0 = 0.0 := byComputing
  let top: Float.ofNat 4294967295 / 4294967296.0 < 1.0 := byComputing
  (rewrite zero at atLeastZero then atLeastZero, floatLeLtTrans _ _ 1.0 atMostTop top)

--| `seededUnit` is in [0, 1).
theorem seededUnitInUnit ∀ (parts: List Float): 0.0 <= seededUnit parts ∧ seededUnit parts < 1.0 :=
  wordUnitInUnit (finalWord parts) (finalWordBelow parts)

-- Settled by computing: the checker computes every float operation on known doubles.

def point (lat lon: Float): LatLon := { lat = { value = lat }, lon = { value = lon } }

--| Outward rounding can pull an edge past the answer when the band is
--| narrower than the rounding error: a tolerance of 1e-13 km (0.1 nm) makes
--| the band [87.6°S, 87.5°S], and the answer, one double below 87.6°S, is
--| outside it. `floorTo (-87.60000000000001) 0.1` is `-87.6`: the quotient
--| by 0.1 rounds up to -876.
theorem narrowLatitudeBandMissesAnswer: inHintBand
      (hintBand (point (-87.60000000000001) 0.0) { value = 1e-13 } Latitude 0.0 1.0)
      (point (-87.60000000000001) 0.0)
      = False :=
  byComputing

--| The same with a tolerance of 2.6e-12 km on longitude, where `wrap`'s own
--| error (2.3e-14° here) is what pushes `from` past the answer.
theorem narrowLongitudeBandMissesAnswer: inHintBand
      (hintBand
        (point (-0.09999999999998391) 106.70000000000003)
        { value = 2.5966564675355047e-12 }
        Longitude
        0.00047574513244963423
        0.9999984769132877)
      (point (-0.09999999999998391) 106.70000000000003)
      = False :=
  byComputing

--| `wrap` is exact on whole degrees but not on tenths, so a narrow longitude
--| band's edges are not the tenths its label shows.
theorem wrapTenth: wrap 0.1 = 0.10000000000002274 := byComputing

theorem wrapWhole: wrap 23.0 = 23.0 ∧ wrap 180.0 = -180.0 ∧ wrap (-180.0) = -180.0 :=
  (byComputing, byComputing, byComputing)

-- `wrap`'s range

theorem natAbsAddBelow ∀ (a b: Int) (bigA bigB bound: Nat)
    (ha: Int.natAbs a ≤ bigA)
    (hb: b = OfNat bigB)
    (h: bigA + bigB < bound):
    Int.natAbs (Int.add a b) < bound :=
  arithmetic [ha, hb, h]

theorem lessToLe ∀ (a b: Nat) (h: a < b): a ≤ b := arithmetic [h]

theorem shiftNonneg ∀ (a: Int) (c: Nat) (ha: Int.natAbs a < c): Int.leq (OfNat 0) (Int.add a (OfNat c)) = True :=
  arithmetic [ha]

theorem lessOfSize ∀ (a: Int) (c: Nat)
    (h0: Int.leq (OfNat 0) a = True)
    (h: Int.natAbs a < c):
    Int.less a (OfNat c) = True :=
  arithmetic [h0, h]

theorem keyBelow ∀ (a b c: Int) (h: Int.less a b = True) (e: c = Int.sub b (OfNat 1)): Int.leq a c = True :=
  arithmetic [h, e]

theorem shiftDown ∀ (a c: Int) (h0: Int.leq (OfNat 0) a = True): Int.leq c (Int.add a c) = True := arithmetic [h0]

theorem shiftLe ∀ (a b c d: Int) (h: Int.leq a b = True) (e: Int.add b c = d): Int.leq (Int.add a c) d = True :=
  arithmetic [h, e]

--| `wrap` puts every finite longitude in [-180°, 180°). `lon + 180.0` is
--| finite; `% 360.0` leaves it below 360 in size; `+ 360.0` then makes it
--| non-negative, and the second `% 360.0` keeps that sign and puts it
--| below 360, so at most 359.99999999999994, the double below; subtracting
--| 180 rounds between -180 and 179.99999999999994.
theorem wrapRange ∀ (lon: Float) (fin: Float.isFinite lon = True): -180.0 <= wrap lon ∧ wrap lon < 180.0 :=
  let p: Nat := Float.Model.pow2 1074
  let f180: Float.isFinite 180.0 = True := byComputing
  let f360: Float.isFinite 360.0 = True := byComputing
  let z360: Float.isZero 360.0 = False := byComputing
  let u360: Float.Theory.units 360.0 = OfNat (p * 360) := byComputing
  let t: Float := lon + 180.0
  let ft: Float.isFinite t = True :=
    Float.Theory.addFiniteOf lon 180.0 fin f180
      (natAbsAddBelow
        (Float.Theory.units lon)
        (Float.Theory.units 180.0)
        (Float.Theory.magUnits 9218868437227405311)
        (p * 180)
        Float.Theory.overflowUnits
        (Float.Theory.unitsAtMostMax lon fin)
        byComputing
        byComputing)
  let u: Float := t % 360.0
  let ru: (Float.isFinite u = True) ∧ (Int.natAbs (Float.Theory.units u) < Int.natAbs (Float.Theory.units 360.0)) :=
    Float.Theory.remUnits t 360.0 ft f360 z360
  let au: Int.natAbs (Float.Theory.units u) < p * 360 :=
    J
      (k w => Int.natAbs (Float.Theory.units u) < k)
      ru.right
      (byComputing: Int.natAbs (Float.Theory.units 360.0) = p * 360)
  let v: Float := u + 360.0
  let fv: Float.isFinite v = True :=
    Float.Theory.addFiniteOf u 360.0 ru.left f360
      (natAbsAddBelow
        (Float.Theory.units u)
        (Float.Theory.units 360.0)
        (p * 360)
        (p * 360)
        Float.Theory.overflowUnits
        (lessToLe (Int.natAbs (Float.Theory.units u)) (p * 360) au)
        u360
        byComputing)
  let v0: 0.0 <= v :=
    Float.Theory.addAtLeast u 360.0 0.0 ru.left f360 byComputing (shiftNonneg (Float.Theory.units u) (p * 360) au) (s =>
      Float.Theory.andFalseRight (Float.Model.signBit u.bits))
  let w: Float := v % 360.0
  let rw: (Float.isFinite w = True) ∧ (Int.natAbs (Float.Theory.units w) < Int.natAbs (Float.Theory.units 360.0)) :=
    Float.Theory.remUnits v 360.0 fv f360 z360
  let w0: 0.0 <= w := Float.remNonneg v 360.0 fv f360 z360 v0
  let uw0: Int.leq (OfNat 0) (Float.Theory.units w) = True := Float.Theory.unitsMonoKey 0 w.bits w0
  let wlt: w < 360.0 :=
    Float.Theory.lessOfUnits w 360.0
      (lessOfSize
        (Float.Theory.units w)
        (p * 360)
        uw0
        (J
          (k z => Int.natAbs (Float.Theory.units w) < k)
          rw.right
          (byComputing: Int.natAbs (Float.Theory.units 360.0) = p * 360)))
  let wle: w <= 359.99999999999994 :=
    keyBelow (Float.orderKey w) (Float.orderKey 360.0) (Float.orderKey 359.99999999999994) wlt byComputing
  let uw: Int.leq (Float.Theory.units w) (Float.Theory.units 359.99999999999994) = True :=
    Float.Theory.unitsMonoKey w.bits 359.99999999999994.bits wle
  let e: w - 180.0 = w + (-180.0) := Float.subAddNeg w 180.0
  let lower: -180.0 <= w + (-180.0) :=
    Float.Theory.addAtLeast w
      (-180.0)
      (-180.0)
      rw.left
      byComputing
      byComputing
      (shiftDown (Float.Theory.units w) (Float.Theory.units (-180.0)) uw0)
      (s => (Bool.trueNotFalse s).impossible)
  let upper: w + (-180.0) <= 179.99999999999994 :=
    Float.Theory.addAtMost w
      (-180.0)
      179.99999999999994
      rw.left
      byComputing
      byComputing
      (shiftLe
        (Float.Theory.units w)
        (Float.Theory.units 359.99999999999994)
        (Float.Theory.units (-180.0))
        (Float.Theory.units 179.99999999999994)
        uw
        byComputing)
      (s => byComputing)
  Both
    (J (y k => -180.0 <= y) lower e.flipped)
    (floatLeLtTrans
      (w - 180.0)
      179.99999999999994
      180.0
      (J (y k => y <= 179.99999999999994) upper e.flipped)
      byComputing)

-- Outward rounding to whole degrees

--| `floorTo x 1.0` is `floor x`: `/ 1.0` and `* 1.0` change nothing, and
--| a whole number survives `* 10.0`, `round` and `/ 10.0`. `|x| < 2^49`
--| keeps `* 10.0` exact; an edge is within 300° of 0.
theorem floorToWhole ∀ (x: Float) (small: Float.abs x < 562949953421312.0): floorTo x 1.0 = Float.floor x :=
  calc floorTo x 1.0
    _ = Float.round (Float.floor (x / 1.0) * 1.0 * 10.0) / 10.0 := byComputing
    _ = Float.round (Float.floor x * 1.0 * 10.0) / 10.0 :=
      Eq.cong (y => Float.round (Float.floor y * 1.0 * 10.0) / 10.0) (Float.divOneRight x)
    _ = Float.round (Float.floor x * 10.0) / 10.0 :=
      Eq.cong (y => Float.round (y * 10.0) / 10.0) (Float.mulOneRight (Float.floor x))
    _ = Float.floor x := Float.roundTenthsOfFloor x small

--| `ceilTo x 1.0` is `ceil x`, as `floorToWhole`.
theorem ceilToWhole ∀ (x: Float) (small: Float.abs x < 562949953421312.0): ceilTo x 1.0 = Float.ceil x := calc ceilTo x
    1.0
  _ = Float.round (Float.ceil (x / 1.0) * 1.0 * 10.0) / 10.0 := byComputing
  _ = Float.round (Float.ceil x * 1.0 * 10.0) / 10.0 :=
    Eq.cong (y => Float.round (Float.ceil y * 1.0 * 10.0) / 10.0) (Float.divOneRight x)
  _ = Float.round (Float.ceil x * 10.0) / 10.0 :=
    Eq.cong (y => Float.round (y * 10.0) / 10.0) (Float.mulOneRight (Float.ceil x))
  _ = Float.ceil x := Float.roundTenthsOfCeil x small

--| Outward rounding to whole degrees contains the unrounded band: the
--| lower edge rounds down and the upper edge rounds up, in the total order
--| (so `-0.0` counts as below `0.0`; `ceilTo -0.5 1.0` is `-0.0`).
theorem outwardRoundingWhole ∀ (from to: Float)
    (smallFrom: Float.abs from < 562949953421312.0)
    (smallTo: Float.abs to < 562949953421312.0):
    floorTo from 1.0 <= from ∧ to <= ceilTo to 1.0 :=
  Both
    (J (y w => y <= from) (Float.floorLe from) (floorToWhole from smallFrom).flipped)
    (J (y w => to <= y) (Float.ceilGe to) (ceilToWhole to smallTo).flipped)

--| A tenth of a degree, `r / 10`, as `floorTo` and `ceilTo` give one.
def tenth (r: Int): Float := Float.ofInt r / 10.0

--| `describeHint`'s rounding to tenths leaves every tenth from -180° to 180°
--| as it is, so the label of an edge that is a tenth is that edge.
theorem tenthsKeepTheirLabel: (List.range 0 3601).all (k =>
      Float.round (tenth (OfNat k - 1800) * 10.0) / 10.0 == tenth (OfNat k - 1800))
      = True :=
  byComputing

-- Latitude's clamps

--| Clamping to [-90°, 90°] lands in it, for every double but the NaN.
theorem latitudeClampRange ∀ (y: Float)
    (ny: Float.isNaN y = False):
    -90.0 <= Float.max (-90.0) (Float.min 90.0 y) ∧ Float.max (-90.0) (Float.min 90.0 y) <= 90.0 :=
  let nm: Float.isNaN (Float.min 90.0 y) = False := Float.minNotNaN 90.0 y byComputing ny
  Both
    (Float.leMaxLeft (-90.0) (Float.min 90.0 y) byComputing nm)
    (Float.maxLe (-90.0) (Float.min 90.0 y) 90.0 byComputing nm byComputing (Float.minLeLeft 90.0 y byComputing ny))

--| Clamping a lower edge at -90° keeps it at most a latitude it was at most.
theorem clampFromKeeps ∀ (lat from: Float)
    (nf: Float.isNaN from = False)
    (low: -90.0 <= lat)
    (h: from <= lat):
    Float.max (-90.0) from <= lat :=
  Float.maxLe (-90.0) from lat byComputing nf low h

--| Clamping an upper edge at 90° keeps it at least a latitude it was at least.
theorem clampToKeeps ∀ (lat to: Float)
    (nt: Float.isNaN to = False)
    (high: lat <= 90.0)
    (h: lat <= to):
    lat <= Float.min 90.0 to :=
  Float.leMin 90.0 to lat byComputing nt high h

-- The margin before rounding

--| `placeAt` puts the answer from 0.15 to 0.85 of the way across, rounding included.
theorem placeAtRange ∀ (unit: Float)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    0.15 <= placeAt unit ∧ placeAt unit <= 0.85 :=
  let c: Float := 1.0 - 2.0 * edge
  let fu: Float.isFinite unit = True := Float.finiteBetween 0.0 unit 1.0 byComputing byComputing low high
  let lo: 0.0 * c <= unit * c := Float.mulMonotoneLeft 0.0 unit c byComputing fu byComputing byComputing low
  let hi: unit * c <= 1.0 * c := Float.mulMonotoneLeft unit 1.0 c fu byComputing byComputing byComputing high
  let lo2: 0.0 <= unit * c := J (y w => y <= unit * c) lo (byComputing: 0.0 * c = 0.0)
  let hi2: unit * c <= 0.7 := J (y w => unit * c <= y) hi (byComputing: 1.0 * c = 0.7)
  let fuc: Float.isFinite (unit * c) = True := Float.finiteBetween 0.0 (unit * c) 0.7 byComputing byComputing lo2 hi2
  let a: edge + 0.0 <= edge + unit * c := Float.addMonotone 0.0 (unit * c) edge byComputing fuc byComputing lo2
  let b: edge + unit * c <= edge + 0.7 := Float.addMonotone (unit * c) 0.7 edge fuc byComputing byComputing hi2
  Both
    (J (y w => y <= edge + unit * c) a (byComputing: edge + 0.0 = 0.15))
    (J (y w => edge + unit * c <= y) b (byComputing: edge + 0.7 = 0.85))

--| A share `a` (0 to 1) of a non-negative finite width is finite and from 0 to the width.
theorem shareOfWidth ∀ (a width: Float)
    (low: 0.0 <= a)
    (high: a <= 1.0)
    (fw: Float.isFinite width = True)
    (w0: 0.0 <= width):
    (Float.isFinite (a * width) = True) ∧ ((0.0 <= a * width) ∧ (a * width <= width)) :=
  let fa: Float.isFinite a = True := Float.finiteBetween 0.0 a 1.0 byComputing byComputing low high
  let lo: 0.0 * width <= a * width := Float.mulMonotoneLeft 0.0 a width byComputing fa fw w0 low
  let hi: a * width <= 1.0 * width := Float.mulMonotoneLeft a 1.0 width fa byComputing fw w0 high
  let lo2: 0.0 <= a * width := J (y w => y <= a * width) lo (Float.zeroMulNonneg width fw w0)
  let one: 1.0 * width = width := Eq.trans (Float.mulCommFinite 1.0 width byComputing fw) (Float.mulOneRight width)
  let hi2: a * width <= width := J (y w => a * width <= y) hi one
  Both (Float.finiteBetween 0.0 (a * width) width byComputing fw lo2 hi2) (Both lo2 hi2)

--| The unrounded lower edge, `lat - placeAt unit * width`, is at least 0.15
--| of the width below the answer and at most 0.85 below it, each product
--| and difference rounded as the code rounds it. The margin over the exact
--| value is a few ulps short of 0.15 · width; bounding that needs the
--| standard error model (NOTES.md).
theorem marginRow ∀ (lat width unit: Float)
    (fl: Float.isFinite lat = True)
    (fw: Float.isFinite width = True)
    (w0: 0.0 <= width)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    lat - 0.85 * width <= lat - placeAt unit * width ∧ lat - placeAt unit * width <= lat - 0.15 * width :=
  let at: Float := placeAt unit
  let r := placeAtRange unit low high
  let atLow: 0.0 <= at := floatLeTrans 0.0 0.15 at byComputing r.left
  let atHigh: at <= 1.0 := floatLeTrans at 0.85 1.0 r.right byComputing
  let fat: Float.isFinite at = True := Float.finiteBetween 0.15 at 0.85 byComputing byComputing r.left r.right
  let s15 := shareOfWidth 0.15 width byComputing byComputing fw w0
  let s85 := shareOfWidth 0.85 width byComputing byComputing fw w0
  let sAt := shareOfWidth at width atLow atHigh fw w0
  Both
    (Float.subAntitoneRight lat
      (at * width)
      (0.85 * width)
      fl
      sAt.left
      s85.left
      (Float.mulMonotoneLeft at 0.85 width fat byComputing fw w0 r.right))
    (Float.subAntitoneRight lat
      (0.15 * width)
      (at * width)
      fl
      s15.left
      sAt.left
      (Float.mulMonotoneLeft 0.15 at width byComputing fat fw w0 r.left))

-- Outward rounding to tenths

--| `floorTo x 0.1` can be a whole ulp of `x` above `x`: from 256° on an ulp
--| is 2^-44, so NOTES.md's earlier bound, `floorTo x 0.1 <= x + 2^-45` for
--| `|x| ≤ 360`, is false. The double one ulp below -359.9 floors to -359.9,
--| 2^-44 above it.
theorem floorToTenthOneUlpAbove: floorTo (-359.90000000000003) 0.1 = -359.9
      ∧ -359.9 - (-359.90000000000003) = 5.684341886080802e-14 :=
  (byComputing, byComputing)

--| The same for `ceilTo`, an ulp below the double one ulp above 256.4.
theorem ceilToTenthOneUlpBelow: ceilTo 256.40000000000003 0.1 = 256.4
      ∧ 256.40000000000003 - 256.4 = 5.684341886080802e-14 :=
  (byComputing, byComputing)
