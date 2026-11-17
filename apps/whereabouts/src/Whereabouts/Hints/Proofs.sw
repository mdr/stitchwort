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

-- Outward rounding to tenths, proved

--| The double for the whole number `i` with sign bit `s`, as `floor`,
--| `ceil` and `round` build it; the sign matters only for zero.
def wholeAt (i: Int) (s: Bool): Float := Float.ofBits (Float.Model.roundScaled i 0 s)

--| What `floorTo` and `ceilTo` give at step 0.1 from the whole number `k` of tenths.
def tenthOf (k: Float): Float := Float.round (k * 0.1 * 10.0) / 10.0

--| 3 · 2^-44: a double this far below a tenth divides by 0.1 to below its
--| whole number of tenths, and it is under 2^-42 even after rounding.
def tenthsSlack: Float := 1.7053025658242404e-13

--| What is checked for each whole number `k` of tenths: the round trip; that
--| `tenthsSlack` below its tenth divides by 0.1 to below `k`, and above it
--| to above `k`; and that the tenth is within 361°.
def tenthsCheck (k: Float): Bool :=
  let whole := Float.round (k * 0.1 * 10.0)
  let t := whole / 10.0
  Nat.equal whole.bits k.bits
    ∧ (Float.less ((t - tenthsSlack) / 0.1) k
      ∧ (Float.less k ((t + tenthsSlack) / 0.1) ∧ (Float.leq (-361.0) t ∧ Float.leq t 361.0)))

def tenthsRow (j: Nat): Bool := tenthsCheck (wholeAt (Int.sub (OfNat j) (OfNat 3601)) False)

--| Every whole number of tenths from -3601 to 3601 passes `tenthsCheck`.
theorem tenthsTable: List.all (List.range 0 (7202 + 1)) tenthsRow = True := byComputing

theorem wholeAtValid ∀ (i: Int) (s: Bool): Float.isValid (Float.Model.roundScaled i 0 s) = True :=
  Float.Theory.roundRatioValid 1 (OfNat 0) s byComputing i

theorem wholeAtOf ∀ (k: Float) (i: Int) (s: Bool) (e: k.bits = Float.Model.roundScaled i 0 s): k = wholeAt i s :=
  Float.bitsExt k
    (wholeAt i s)
    (Eq.trans e (Float.Theory.ofBitsBits (Float.Model.roundScaled i 0 s) (wholeAtValid i s)).flipped)

theorem tenthsRowIndex ∀ (i: Int)
    (h: Int.natAbs i ≤ 3601):
    Int.sub (OfNat (Int.natAbs (Int.add i (OfNat 3601)))) (OfNat 3601) = i :=
  arithmetic [h]

theorem tenthsRowBelow ∀ (i: Int) (h: Int.natAbs i ≤ 3601): Int.natAbs (Int.add i (OfNat 3601)) ≤ 7202 := arithmetic [h]

--| Every whole number of tenths up to 3601 in size, of either zero sign, passes `tenthsCheck`.
theorem tenthsAt ∀ (i: Int) (s: Bool) (h: Int.natAbs i ≤ 3601): tenthsCheck (wholeAt i s) = True :=
  let j: Nat := Int.natAbs (Int.add i (OfNat 3601))
  let row: tenthsRow j = True :=
    List.allBetweenElim [q := tenthsRow] [lo := 0] [hi := 7202] tenthsTable [k := j] (arithmetic) (tenthsRowBelow i h)
  let plain: tenthsCheck (wholeAt i False) = True :=
    J (y w => tenthsCheck (wholeAt y False) = True) row (tenthsRowIndex i h)
  match s with
    | False => plain
    | True =>
      Float.Theory.orCase
        [goal := tenthsCheck (wholeAt i True) = True]
        (Float.Theory.intZeroCases i)
        (i0 =>
          J
            (y w => tenthsCheck (wholeAt y True) = True)
            (byComputing: tenthsCheck (wholeAt (OfNat 0) True) = True)
            i0.flipped)
        (nz =>
          J
            (b w => tenthsCheck (Float.ofBits b) = True)
            plain
            (Float.Theory.roundRatioSignIrrelevant 1 (OfNat 0) False True i nz))

theorem roundTripOf ∀ (k: Float) (c: tenthsCheck k = True): Float.round (k * 0.1 * 10.0) = k :=
  Float.bitsExt
    (Float.round (k * 0.1 * 10.0))
    k
    (Nat.equalSound (Float.round (k * 0.1 * 10.0)).bits k.bits (Bool.andLeft c))

--| The round trip in `floorTo` and `ceilTo` at step 0.1: a whole double `k`
--| of `n` (up to 3601 in size) comes back from `round (k * 0.1 * 10.0)`,
--| though neither product need be exact. Checked for each `n`, by computing,
--| zeros of both signs included.
theorem tenthsRoundTrip ∀ (k: Float) (n: Int)
    (fk: Float.isFinite k = True)
    (whole: Float.Theory.units k = Int.mul n (OfNat (Float.Model.pow2 1074)))
    (h: Int.natAbs n ≤ 3601):
    Float.round (k * 0.1 * 10.0) = k :=
  let a: Nat := k.bits
  let sb: Bool := Float.Model.signBit a
  let e: k.bits = Float.Model.roundScaled n 0 sb := calc k.bits
    _ = Float.Model.roundRatio (Float.Model.units a) 1 (-1074) sb :=
      (Float.Theory.roundRatioUnitsBits a (Float.Theory.finiteBits k fk)).flipped
    _ = Float.Model.roundRatio (Int.mul n (OfNat (Float.Model.pow2 1074))) 1 (-1074) sb :=
      Eq.cong (u => Float.Model.roundRatio u 1 (-1074) sb) whole
    _ = Float.Model.roundScaled n 0 sb := (Float.Theory.roundWhole n sb).flipped
  roundTripOf k (J (y w => tenthsCheck y = True) (tenthsAt n sb h) (wholeAtOf k n sb e).flipped)

theorem unitsWithin ∀ (u lo hi: Int) (p: Nat)
    (pp: 0 < p)
    (el: lo = Int.neg (OfNat (p * 3600)))
    (eh: hi = OfNat (p * 3600))
    (a: Int.leq lo u = True)
    (b: Int.leq u hi = True):
    Int.natAbs u < p * 3601 :=
  arithmetic [pp, el, eh, a, b]

--| `x / 0.1` for `|x| ≤ 360` is finite and under 3601 in size.
theorem tenthsQuotient ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    (Float.isFinite (x / 0.1) = True) ∧ (Int.natAbs (Float.Theory.units (x / 0.1)) < Float.Model.pow2 1074 * 3601) :=
  let y: Float := x / 0.1
  let pos: 0.0 < 0.1 := byComputing
  let f01: Float.isFinite 0.1 = True := byComputing
  let ylo: -3600.0 <= y :=
    J (z w => z <= y) (Float.divMonotone (-360.0) x 0.1 pos f01 lo) (byComputing: -360.0 / 0.1 = -3600.0)
  let yhi: y <= 3600.0 :=
    J (z w => y <= z) (Float.divMonotone x 360.0 0.1 pos f01 hi) (byComputing: 360.0 / 0.1 = 3600.0)
  Both
    (Float.finiteBetween (-3600.0) y 3600.0 byComputing byComputing ylo yhi)
    (unitsWithin
      (Float.Theory.units y)
      (Float.Theory.units (-3600.0))
      (Float.Theory.units 3600.0)
      (Float.Model.pow2 1074)
      byComputing
      byComputing
      byComputing
      (Float.Theory.unitsMonoKey (-3600.0).bits y.bits ylo)
      (Float.Theory.unitsMonoKey y.bits 3600.0.bits yhi))

--| For `|x| ≤ 360`, `floor (x / 0.1)` is a whole number of tenths that passes `tenthsCheck`.
theorem floorTenthsChecked ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    tenthsCheck (Float.floor (x / 0.1)) = True :=
  let y: Float := x / 0.1
  let q := tenthsQuotient x lo hi
  let a: Nat := y.bits
  let s: Bool := Float.Model.signBit a
  let n: Nat := Int.natAbs (Float.Model.units a)
  let f: Int := Float.Model.floorDiv s n (Float.Model.pow2 1074)
  let fb: Int.natAbs f ≤ 3601 := Float.Theory.floorDivBelow s n (Float.Model.pow2 1074) 3601 byComputing q.right
  let fl: (Float.floor y).bits = Float.Model.roundScaled f 0 s :=
    Eq.trans
      (Float.Theory.floorOfBits y)
      (Float.Theory.floorFinite a (Float.Theory.notSpecialOf a (Float.Theory.finiteBits y q.left)))
  J (k w => tenthsCheck k = True) (tenthsAt f s fb) (wholeAtOf (Float.floor y) f s fl).flipped

theorem natAbsNegAtMost ∀ (g: Int) (h: Int.natAbs g ≤ 3601): Int.natAbs (Int.neg g) ≤ 3601 := arithmetic [h]

--| The same for `ceil (x / 0.1)`.
theorem ceilTenthsChecked ∀ (x: Float) (lo: -360.0 <= x) (hi: x <= 360.0): tenthsCheck (Float.ceil (x / 0.1)) = True :=
  let y: Float := x / 0.1
  let q := tenthsQuotient x lo hi
  let a: Nat := y.bits
  let s: Bool := Float.Model.signBit a
  let n: Nat := Int.natAbs (Float.Model.units a)
  let g: Int := Float.Model.floorDiv (¬s) n (Float.Model.pow2 1074)
  let gb: Int.natAbs g ≤ 3601 := Float.Theory.floorDivBelow (¬s) n (Float.Model.pow2 1074) 3601 byComputing q.right
  let cl: (Float.ceil y).bits = Float.Model.roundScaled (Int.neg g) 0 s :=
    Eq.trans
      (Float.Theory.ceilOfBits y)
      (Float.Theory.ceilFinite a (Float.Theory.notSpecialOf a (Float.Theory.finiteBits y q.left)))
  J
    (k w => tenthsCheck k = True)
    (tenthsAt (Int.neg g) s (natAbsNegAtMost g gb))
    (wholeAtOf (Float.ceil y) (Int.neg g) s cl).flipped

--| `floorTo x 0.1` is the floor of `x / 0.1` over ten, for `|x| ≤ 360`.
theorem floorToTenth ∀ (x: Float) (lo: -360.0 <= x) (hi: x <= 360.0): floorTo x 0.1 = Float.floor (x / 0.1) / 10.0 :=
  Eq.cong (r => r / 10.0) (roundTripOf (Float.floor (x / 0.1)) (floorTenthsChecked x lo hi))

--| `ceilTo x 0.1` is the ceiling of `x / 0.1` over ten, for `|x| ≤ 360`.
theorem ceilToTenth ∀ (x: Float) (lo: -360.0 <= x) (hi: x <= 360.0): ceilTo x 0.1 = Float.ceil (x / 0.1) / 10.0 :=
  Eq.cong (r => r / 10.0) (roundTripOf (Float.ceil (x / 0.1)) (ceilTenthsChecked x lo hi))

theorem intNegOfNotNonneg ∀ (a: Int) (h: Int.leq (OfNat 0) a = False): Int.less a (OfNat 0) = True := arithmetic [h]

theorem intLeOfLess ∀ (a b: Int) (h: Int.less a b = True): Int.leq a b = True := arithmetic [h]

theorem intLeTransOf ∀ (a b c: Int) (ab: Int.leq a b = True) (bc: Int.leq b c = True): Int.leq a c = True :=
  arithmetic [ab, bc]

theorem floatLeOfLt ∀ (x y: Float) (h: x < y): x <= y :=
  let a: Int.less (Float.orderKey x) (Float.orderKey y) = True := h
  (arithmetic: Int.leq (Float.orderKey x) (Float.orderKey y) = True)

theorem floatLtIrrefl ∀ (x: Float) (h: x < x): Void :=
  Float.Theory.intLeLessAbsurd (Float.orderKey x) (Float.orderKey x) (arithmetic) h

--| If a double `c` below `x`'s tenth divides by 0.1 to below `floor (x / 0.1)`,
--| `x` is at least `c`, so anything at most `E` units above `c` is at most
--| `E` above `x`.
theorem floorTenthBelow ∀ (x c: Float) (g: Int) (e: Nat)
    (lt: c / 0.1 < Float.floor (x / 0.1))
    (close: Int.leq g (Int.add (Float.Theory.units c) (OfNat e)) = True):
    Int.leq g (Int.add (Float.Theory.units x) (OfNat e)) = True :=
  let k: Float := Float.floor (x / 0.1)
  Float.Theory.orCase
    [goal := Int.leq g (Int.add (Float.Theory.units x) (OfNat e)) = True]
    (Float.Theory.boolCases (Int.less (Float.Theory.units x) (Float.Theory.units c)))
    (below =>
      let q: x / 0.1 <= c / 0.1 :=
        Float.divMonotone x c 0.1 byComputing byComputing (floatLeOfLt x c (Float.Theory.lessOfUnits x c below))
      let kc: k <= c / 0.1 := floatLeTrans k (x / 0.1) (c / 0.1) (Float.floorLe (x / 0.1)) q
      (floatLtIrrefl k (floatLeLtTrans k (c / 0.1) k kc lt)).impossible)
    (notBelow => arithmetic [notBelow, close])

--| The same for `ceil (x / 0.1)` and a double `c` above `x`'s tenth.
theorem ceilTenthAbove ∀ (x c: Float) (g: Int) (e: Nat)
    (lt: Float.ceil (x / 0.1) < c / 0.1)
    (close: Int.leq (Float.Theory.units c) (Int.add g (OfNat e)) = True):
    Int.leq (Float.Theory.units x) (Int.add g (OfNat e)) = True :=
  let k: Float := Float.ceil (x / 0.1)
  Float.Theory.orCase
    [goal := Int.leq (Float.Theory.units x) (Int.add g (OfNat e)) = True]
    (Float.Theory.boolCases (Int.less (Float.Theory.units c) (Float.Theory.units x)))
    (above =>
      let q: c / 0.1 <= x / 0.1 :=
        Float.divMonotone c x 0.1 byComputing byComputing (floatLeOfLt c x (Float.Theory.lessOfUnits c x above))
      let ck: c / 0.1 <= k := floatLeTrans (c / 0.1) (x / 0.1) k q (Float.ceilGe (x / 0.1))
      (floatLtIrrefl (c / 0.1) (floatLeLtTrans (c / 0.1) k (c / 0.1) ck lt)).impossible)
    (notAbove => arithmetic [notAbove, close])

--| A sum of `g` within 361° (`g` in units of 2^-1074, `w` = 2^1030) and
--| `n`: the rounded sum `s` is at least `g + n` less one `w`. The standard
--| model bounds `s`'s size; the sign cases give its direction.
theorem roundedSumAbove ∀ (g n s: Int) (w t: Nat)
    (w2: 2 ≤ w)
    (gLo: Int.leq (Int.neg (OfNat (w * 6350779162034176))) g = True)
    (gHi: Int.leq g (OfNat (w * 6350779162034176)) = True)
    (nSize: Int.natAbs n = 3 * w)
    (err: Nat.absDiff (Int.natAbs s * 1) (Int.natAbs (Int.add g n)) * 9007199254740992
      ≤ Int.natAbs (Int.add g n) + 1 * 4503599627370496)
    (sign: ((Int.leq (OfNat 0) (Int.add g n) = True) ∧ (Int.leq (OfNat 0) s = True))
      ∨ ((Int.less (Int.add g n) (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True))):
    (Int.leq (Int.add g n) (Int.add s (OfNat w)) = True) ∧ (Int.leq s (Int.add (Int.add g n) (OfNat w)) = True) :=
  match sign with
    | Inl b =>
      let b1 := b.left
      let b2 := b.right
      Both (arithmetic [w2, gLo, gHi, nSize, err, b1, b2]) (arithmetic [w2, gLo, gHi, nSize, err, b1, b2])
    | Inr b =>
      let b1 := b.left
      let b2 := b.right
      Both (arithmetic [w2, gLo, gHi, nSize, err, b1, b2]) (arithmetic [w2, gLo, gHi, nSize, err, b1, b2])

theorem sumSmall ∀ (g n: Int) (w t: Nat)
    (w2: 2 ≤ w)
    (gLo: Int.leq (Int.neg (OfNat (w * 6350779162034176))) g = True)
    (gHi: Int.leq g (OfNat (w * 6350779162034176)) = True)
    (nSize: Int.natAbs n = 3 * w)
    (top: w * 1000000000000000000 ≤ t):
    Int.natAbs (Int.add g n) < t :=
  arithmetic [w2, gLo, gHi, nSize, top]

--| Adding `d`, 3 · 2^-44 in size, to a `g` within 361°: the rounded sum is
--| within 2^-44 of the exact one, in units of 2^-1074.
theorem slackSum ∀ (g d: Float)
    (fd: Float.isFinite d = True)
    (dSize: Int.natAbs (Float.Theory.units d) = 3 * Float.Model.pow2 1030)
    (lo: -361.0 <= g)
    (hi: g <= 361.0)
    (flo: Float.isFinite (-361.0 + d) = True)
    (fhi: Float.isFinite (361.0 + d) = True):
    (Int.leq
      (Int.add (Float.Theory.units g) (Float.Theory.units d))
      (Int.add (Float.Theory.units (g + d)) (OfNat (Float.Model.pow2 1030)))
      = True)
      ∧ (Int.leq
        (Float.Theory.units (g + d))
        (Int.add (Int.add (Float.Theory.units g) (Float.Theory.units d)) (OfNat (Float.Model.pow2 1030)))
        = True) :=
  let w: Nat := Float.Model.pow2 1030
  let fg: Float.isFinite g = True := Float.finiteBetween (-361.0) g 361.0 byComputing byComputing lo hi
  let fs: Float.isFinite (g + d) = True :=
    Float.finiteBetween
      (-361.0 + d)
      (g + d)
      (361.0 + d)
      flo
      fhi
      (Float.addMonotoneLeft (-361.0) g d byComputing fg fd lo)
      (Float.addMonotoneLeft g 361.0 d fg byComputing fd hi)
  let gLo: Int.leq (Int.neg (OfNat (w * 6350779162034176))) (Float.Theory.units g) = True :=
    J
      (y z => Int.leq y (Float.Theory.units g) = True)
      (Float.Theory.unitsMonoKey (-361.0).bits g.bits lo)
      (byComputing: Float.Theory.units (-361.0) = Int.neg (OfNat (w * 6350779162034176)))
  let gHi: Int.leq (Float.Theory.units g) (OfNat (w * 6350779162034176)) = True :=
    J
      (y z => Int.leq (Float.Theory.units g) y = True)
      (Float.Theory.unitsMonoKey g.bits 361.0.bits hi)
      (byComputing: Float.Theory.units 361.0 = OfNat (w * 6350779162034176))
  let w2: 2 ≤ w := byComputing
  let sum: Int := Int.add (Float.Theory.units g) (Float.Theory.units d)
  let s: Int := Float.Theory.units (g + d)
  let err :=
    Float.addRelError g d fg fd fs
      (sumSmall (Float.Theory.units g) (Float.Theory.units d) w (1 * Nat.pow 2 2097) w2 gLo gHi dSize byComputing)
  let zero: Float.Theory.units 0.0 = OfNat 0 := byComputing
  let negZero: Float.Theory.units (-0.0) = OfNat 0 := byComputing
  let sign: ((Int.leq (OfNat 0) sum = True) ∧ (Int.leq (OfNat 0) s = True))
    ∨ ((Int.less sum (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True)) :=
    Float.Theory.orCase
      [goal := ((Int.leq (OfNat 0) sum = True) ∧ (Int.leq (OfNat 0) s = True))
        ∨ ((Int.less sum (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True))]
      (Float.Theory.boolCases (Int.leq (OfNat 0) sum))
      (nonneg =>
        let atLeast: -0.0 <= g + d :=
          Float.Theory.addAtLeast g d
            (-0.0)
            fg
            fd
            byComputing
            (J (y z => Int.leq y sum = True) nonneg negZero.flipped)
            (b => (Bool.trueNotFalse b).impossible)
        Inl
          (Both nonneg
            (J (y z => Int.leq y s = True) (Float.Theory.unitsMonoKey (-0.0).bits (g + d).bits atLeast) negZero)))
      (neg =>
        let below: Int.less sum (OfNat 0) = True := intNegOfNotNonneg sum neg
        let atMost: g + d <= 0.0 :=
          Float.Theory.addAtMost g d 0.0 fg fd byComputing
            (J (y z => Int.leq sum y = True) (intLeOfLess sum (OfNat 0) below) zero.flipped)
            (b => byComputing)
        Inr (Both below (J (y z => Int.leq s y = True) (Float.Theory.unitsMonoKey (g + d).bits 0.0.bits atMost) zero)))
  roundedSumAbove (Float.Theory.units g) (Float.Theory.units d) s w (1 * Nat.pow 2 2097) w2 gLo gHi dSize err sign

theorem slackCloseBelow ∀ (g d c: Int) (w e: Nat)
    (ed: d = Int.neg (OfNat (3 * w)))
    (ee: e = 4 * w)
    (h: Int.leq (Int.add g d) (Int.add c (OfNat w)) = True):
    Int.leq g (Int.add c (OfNat e)) = True :=
  arithmetic [ed, ee, h]

theorem slackCloseAbove ∀ (g d c: Int) (w e: Nat)
    (ed: d = OfNat (3 * w))
    (ee: e = 4 * w)
    (h: Int.leq c (Int.add (Int.add g d) (OfNat w)) = True):
    Int.leq c (Int.add g (OfNat e)) = True :=
  arithmetic [ed, ee, h]

--| Outward rounding to tenths moves a lower edge up by at most 2^-42, for
--| `|x| ≤ 360`: `floorTo x 0.1 ≤ x + 2^-42` in exact units of 2^-1074. It
--| can be above `x` (`floorToTenthOneUlpAbove`), which is why the band
--| needs a margin.
--|
--| The proof: `floor (x / 0.1)` is a whole number `k` of tenths up to 3601
--| in size, and for each such `k`, by computing, the double `c` 3 · 2^-44
--| below `tenthOf k` divides by 0.1 to below `k` (`tenthsCheck`). If `x`
--| were below `c`, monotonicity of `/ 0.1` and `floor x ≤ x` would put `k`
--| below itself; so `x ≥ c`, and `c` is within 2^-44 of its exact value by
--| the standard model for `+` (`slackSum`).
theorem floorToTenthBound ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    Int.leq (Float.Theory.units (floorTo x 0.1)) (Int.add (Float.Theory.units x) (OfNat (Float.Model.pow2 1032)))
      = True :=
  let k: Float := Float.floor (x / 0.1)
  let g: Float := tenthOf k
  let rest := Bool.andRight (floorTenthsChecked x lo hi)
  let lt: (g - tenthsSlack) / 0.1 < k := Bool.andLeft rest
  let bounds := Bool.andRight (Bool.andRight rest)
  let d: Float := -tenthsSlack
  let sum := slackSum g d byComputing byComputing (Bool.andLeft bounds) (Bool.andRight bounds) byComputing byComputing
  let e: g - tenthsSlack = g + d := Float.subAddNeg g tenthsSlack
  let close: Int.leq
    (Float.Theory.units g)
    (Int.add (Float.Theory.units (g - tenthsSlack)) (OfNat (Float.Model.pow2 1032)))
    = True :=
    slackCloseBelow
      (Float.Theory.units g)
      (Float.Theory.units d)
      (Float.Theory.units (g - tenthsSlack))
      (Float.Model.pow2 1030)
      (Float.Model.pow2 1032)
      byComputing
      byComputing
      (J
        (y z =>
          Int.leq
            (Int.add (Float.Theory.units g) (Float.Theory.units d))
            (Int.add (Float.Theory.units y) (OfNat (Float.Model.pow2 1030)))
            = True)
        sum.left
        e.flipped)
  floorTenthBelow x (g - tenthsSlack) (Float.Theory.units g) (Float.Model.pow2 1032) lt close

--| Outward rounding to tenths moves an upper edge down by at most 2^-42,
--| for `|x| ≤ 360`: `x ≤ ceilTo x 0.1 + 2^-42` in exact units, as
--| `floorToTenthBound`.
theorem ceilToTenthBound ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    Int.leq (Float.Theory.units x) (Int.add (Float.Theory.units (ceilTo x 0.1)) (OfNat (Float.Model.pow2 1032)))
      = True :=
  let k: Float := Float.ceil (x / 0.1)
  let g: Float := tenthOf k
  let rest := Bool.andRight (Bool.andRight (ceilTenthsChecked x lo hi))
  let lt: k < (g + tenthsSlack) / 0.1 := Bool.andLeft rest
  let bounds := Bool.andRight rest
  let sum :=
    slackSum g tenthsSlack byComputing byComputing (Bool.andLeft bounds) (Bool.andRight bounds) byComputing byComputing
  let close: Int.leq
    (Float.Theory.units (g + tenthsSlack))
    (Int.add (Float.Theory.units g) (OfNat (Float.Model.pow2 1032)))
    = True :=
    slackCloseAbove
      (Float.Theory.units g)
      (Float.Theory.units tenthsSlack)
      (Float.Theory.units (g + tenthsSlack))
      (Float.Model.pow2 1030)
      (Float.Model.pow2 1032)
      byComputing
      byComputing
      sum.right
  ceilTenthAbove x (g + tenthsSlack) (Float.Theory.units g) (Float.Model.pow2 1032) lt close

-- The margin, exactly

theorem roundedSumNear ∀ (g n s: Int) (w: Nat)
    (w2: 2 ≤ w)
    (gLo: Int.leq (Int.neg (OfNat (w * 6350779162034176))) g = True)
    (gHi: Int.leq g (OfNat (w * 6350779162034176)) = True)
    (nLo: Int.leq (Int.neg (OfNat (w * 6350779162034176))) n = True)
    (nHi: Int.leq n (OfNat (w * 6350779162034176)) = True)
    (err: Nat.absDiff (Int.natAbs s * 1) (Int.natAbs (Int.add g n)) * 9007199254740992
      ≤ Int.natAbs (Int.add g n) + 1 * 4503599627370496)
    (sign: ((Int.leq (OfNat 0) (Int.add g n) = True) ∧ (Int.leq (OfNat 0) s = True))
      ∨ ((Int.less (Int.add g n) (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True))):
    (Int.leq (Int.add g n) (Int.add s (OfNat (w * 2))) = True)
      ∧ (Int.leq s (Int.add (Int.add g n) (OfNat (w * 2))) = True) :=
  match sign with
    | Inl b =>
      let b1 := b.left
      let b2 := b.right
      Both (arithmetic [w2, gLo, gHi, nLo, nHi, err, b1, b2]) (arithmetic [w2, gLo, gHi, nLo, nHi, err, b1, b2])
    | Inr b =>
      let b1 := b.left
      let b2 := b.right
      Both (arithmetic [w2, gLo, gHi, nLo, nHi, err, b1, b2]) (arithmetic [w2, gLo, gHi, nLo, nHi, err, b1, b2])

theorem sumSmallNear ∀ (g n: Int) (w t: Nat)
    (w2: 2 ≤ w)
    (gLo: Int.leq (Int.neg (OfNat (w * 6350779162034176))) g = True)
    (gHi: Int.leq g (OfNat (w * 6350779162034176)) = True)
    (nLo: Int.leq (Int.neg (OfNat (w * 6350779162034176))) n = True)
    (nHi: Int.leq n (OfNat (w * 6350779162034176)) = True)
    (top: w * 1000000000000000000 ≤ t):
    Int.natAbs (Int.add g n) < t :=
  arithmetic [w2, gLo, gHi, nLo, nHi, top]

theorem unitsWithin361 ∀ (g: Float)
    (lo: -361.0 <= g)
    (hi: g <= 361.0):
    (Int.leq (Int.neg (OfNat (Float.Model.pow2 1030 * 6350779162034176))) (Float.Theory.units g) = True)
      ∧ (Int.leq (Float.Theory.units g) (OfNat (Float.Model.pow2 1030 * 6350779162034176)) = True) :=
  Both
    (J
      (y z => Int.leq y (Float.Theory.units g) = True)
      (Float.Theory.unitsMonoKey (-361.0).bits g.bits lo)
      (byComputing: Float.Theory.units (-361.0) = Int.neg (OfNat (Float.Model.pow2 1030 * 6350779162034176))))
    (J
      (y z => Int.leq (Float.Theory.units g) y = True)
      (Float.Theory.unitsMonoKey g.bits 361.0.bits hi)
      (byComputing: Float.Theory.units 361.0 = OfNat (Float.Model.pow2 1030 * 6350779162034176)))

--| The sum of two doubles within 361° is at most 2^-43 above the exact
--| sum, in units of 2^-1074: the standard model for `+`, with the sign
--| of the rounded sum following the exact one's.
theorem sumNear ∀ (g d: Float)
    (lo: -361.0 <= g)
    (hi: g <= 361.0)
    (dLo: -361.0 <= d)
    (dHi: d <= 361.0):
    (Float.isFinite (g + d) = True)
      ∧ ((Int.leq
        (Int.add (Float.Theory.units g) (Float.Theory.units d))
        (Int.add (Float.Theory.units (g + d)) (OfNat (Float.Model.pow2 1030 * 2)))
        = True)
        ∧ (Int.leq
          (Float.Theory.units (g + d))
          (Int.add (Int.add (Float.Theory.units g) (Float.Theory.units d)) (OfNat (Float.Model.pow2 1030 * 2)))
          = True)) :=
  let w: Nat := Float.Model.pow2 1030
  let fg: Float.isFinite g = True := Float.finiteBetween (-361.0) g 361.0 byComputing byComputing lo hi
  let fd: Float.isFinite d = True := Float.finiteBetween (-361.0) d 361.0 byComputing byComputing dLo dHi
  let fs: Float.isFinite (g + d) = True :=
    Float.finiteBetween
      (-361.0 + -361.0)
      (g + d)
      (361.0 + 361.0)
      byComputing
      byComputing
      (floatLeTrans
        (-361.0 + -361.0)
        (-361.0 + d)
        (g + d)
        (Float.addMonotone (-361.0) d (-361.0) byComputing fd byComputing dLo)
        (Float.addMonotoneLeft (-361.0) g d byComputing fg fd lo))
      (floatLeTrans
        (g + d)
        (361.0 + d)
        (361.0 + 361.0)
        (Float.addMonotoneLeft g 361.0 d fg byComputing fd hi)
        (Float.addMonotone d 361.0 361.0 fd byComputing byComputing dHi))
  let gb := unitsWithin361 g lo hi
  let db := unitsWithin361 d dLo dHi
  let w2: 2 ≤ w := byComputing
  let sum: Int := Int.add (Float.Theory.units g) (Float.Theory.units d)
  let s: Int := Float.Theory.units (g + d)
  let err :=
    Float.addRelError g d fg fd fs
      (sumSmallNear
        (Float.Theory.units g)
        (Float.Theory.units d)
        w
        (1 * Nat.pow 2 2097)
        w2
        gb.left
        gb.right
        db.left
        db.right
        byComputing)
  let zero: Float.Theory.units 0.0 = OfNat 0 := byComputing
  let negZero: Float.Theory.units (-0.0) = OfNat 0 := byComputing
  let sign: ((Int.leq (OfNat 0) sum = True) ∧ (Int.leq (OfNat 0) s = True))
    ∨ ((Int.less sum (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True)) :=
    Float.Theory.orCase
      [goal := ((Int.leq (OfNat 0) sum = True) ∧ (Int.leq (OfNat 0) s = True))
        ∨ ((Int.less sum (OfNat 0) = True) ∧ (Int.leq s (OfNat 0) = True))]
      (Float.Theory.boolCases (Int.leq (OfNat 0) sum))
      (nonneg =>
        let atLeast: -0.0 <= g + d :=
          Float.Theory.addAtLeast g d
            (-0.0)
            fg
            fd
            byComputing
            (J (y z => Int.leq y sum = True) nonneg negZero.flipped)
            (b => (Bool.trueNotFalse b).impossible)
        Inl
          (Both nonneg
            (J (y z => Int.leq y s = True) (Float.Theory.unitsMonoKey (-0.0).bits (g + d).bits atLeast) negZero)))
      (neg =>
        let below: Int.less sum (OfNat 0) = True := intNegOfNotNonneg sum neg
        let atMost: g + d <= 0.0 :=
          Float.Theory.addAtMost g d 0.0 fg fd byComputing
            (J (y z => Int.leq sum y = True) (intLeOfLess sum (OfNat 0) below) zero.flipped)
            (b => byComputing)
        Inr (Both below (J (y z => Int.leq s y = True) (Float.Theory.unitsMonoKey (g + d).bits 0.0.bits atMost) zero)))
  Both fs
    (roundedSumNear (Float.Theory.units g) (Float.Theory.units d) s w w2 gb.left gb.right db.left db.right err sign)

theorem marginArith ∀ (l d s f: Int) (w e: Nat)
    (ee: e = w * 4)
    (dHi: Int.leq d (Int.neg (OfNat (w * 6))) = True)
    (near: Int.leq s (Int.add (Int.add l d) (OfNat (w * 2))) = True)
    (fs: Int.leq f s = True):
    Int.leq (Int.add f (OfNat e)) l = True :=
  arithmetic [ee, dHi, near, fs]

--| The exact margin at the lower edge: for a band at least 1e-11° wide, the
--| unrounded lower edge `lat - placeAt unit * width` is at least 2^-42
--| below the answer, in exact units, so `floorTo`'s error at step 0.1
--| (`floorToTenthBound`) can't carry it past the answer. (The margin is
--| 0.15 of the width; 1e-11° is far below any real band.)
--|
--| The proof: the edge is at most `lat - 0.15 * width` (`marginRow`), and
--| `0.15 * width` is at least `0.15 * 1e-11`, over 6 · 2^-44; the standard
--| model for the subtraction (`sumNear`) loses at most 2^-43 of it.
theorem marginBelowExact ∀ (lat width unit: Float)
    (latLo: -361.0 <= lat)
    (latHi: lat <= 361.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 361.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    Int.leq
      (Int.add (Float.Theory.units (lat - placeAt unit * width)) (OfNat (Float.Model.pow2 1032)))
      (Float.Theory.units lat)
      = True :=
  let fl: Float.isFinite lat = True := Float.finiteBetween (-361.0) lat 361.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 361.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := floatLeTrans 0.0 1e-11 width byComputing wLo
  let row := marginRow lat width unit fl fw w0 low high
  let q: Float := 0.15 * width
  let sq := shareOfWidth 0.15 width byComputing byComputing fw w0
  let qLo: 0.15 * 1e-11 <= q :=
    J
      (y z => 0.15 * 1e-11 <= y)
      (J
        (y z => y <= width * 0.15)
        (Float.mulMonotoneLeft 1e-11 width 0.15 byComputing fw byComputing byComputing wLo)
        (byComputing: 1e-11 * 0.15 = 0.15 * 1e-11))
      (Float.mulCommFinite width 0.15 fw byComputing)
  let qHi: q <= 361.0 := floatLeTrans q width 361.0 sq.right.right wHi
  let nq: Float.isNaN q = False := Float.Theory.finiteNotNaN q.bits (Float.Theory.finiteBits q sq.left)
  let d: Float := -q
  let dHi: d <= -(0.15 * 1e-11) := Float.negAntitone (0.15 * 1e-11) q byComputing nq qLo
  let dLo: -361.0 <= d := Float.negAntitone q 361.0 nq byComputing qHi
  let e: lat - q = lat + d := Float.subAddNeg lat q
  let near := (sumNear lat d latLo latHi dLo (floatLeTrans d (-(0.15 * 1e-11)) 361.0 dHi byComputing)).right.right
  let du: Int.leq (Float.Theory.units d) (Int.neg (OfNat (Float.Model.pow2 1030 * 6))) = True :=
    intLeTransOf
      (Float.Theory.units d)
      (Float.Theory.units (-(0.15 * 1e-11)))
      (Int.neg (OfNat (Float.Model.pow2 1030 * 6)))
      (Float.Theory.unitsMonoKey d.bits (-(0.15 * 1e-11)).bits dHi)
      byComputing
  let edge: Int.leq (Float.Theory.units (lat - placeAt unit * width)) (Float.Theory.units (lat + d)) = True :=
    J
      (y z => Int.leq (Float.Theory.units (lat - placeAt unit * width)) (Float.Theory.units y) = True)
      (Float.Theory.unitsMonoKey (lat - placeAt unit * width).bits (lat - q).bits row.right)
      e
  marginArith
    (Float.Theory.units lat)
    (Float.Theory.units d)
    (Float.Theory.units (lat + d))
    (Float.Theory.units (lat - placeAt unit * width))
    (Float.Model.pow2 1030)
    (Float.Model.pow2 1032)
    byComputing
    du
    near
    edge

theorem signFlip ∀ (n: Nat)
    (v: n < 18446744073709551616):
    Float.Model.signBit (Float.flipSignBits n) = ¬(Float.Model.signBit n) :=
  match c: Nat.leq 9223372036854775808 n with
    | True =>
      let c2: Nat.leq 9223372036854775808 (n - 9223372036854775808) = False := arithmetic [c, v]
      rewrite c2
    | False =>
      let c2: Nat.leq 9223372036854775808 (n + 9223372036854775808) = True := arithmetic
      rewrite c2

theorem signedNot ∀ (s: Bool) (m: Nat): Int.signed (¬s) m = Int.neg (Int.signed s m) := match s with
  | True => Float.Theory.signedFlip False m
  | False => Float.Theory.signedFlip True m

--| Negation negates units, for every double but the NaN.
theorem unitsNeg ∀ (x: Float) (nx: Float.isNaN x = False): Float.Theory.units (-x) = Int.neg (Float.Theory.units x) :=
  let n: Nat := x.bits
  let v: n < 18446744073709551616 := Float.Theory.bitsBelow x
  let flip: Float.Model.units (Float.flipSignBits n) = Int.neg (Float.Model.units n) := calc Float.Model.units
    (Float.flipSignBits n)
    _ = Int.signed
        (Float.Model.signBit (Float.flipSignBits n))
        (Float.Theory.magUnits (Float.Model.magnitude (Float.flipSignBits n))) :=
      Float.Theory.unitsMag (Float.flipSignBits n)
    _ = Int.signed (¬(Float.Model.signBit n)) (Float.Theory.magUnits (Float.Model.magnitude n)) :=
      Eq.cong2 (s m => Int.signed s (Float.Theory.magUnits m)) (signFlip n v) (Float.Theory.magFlip n v)
    _ = Int.neg (Int.signed (Float.Model.signBit n) (Float.Theory.magUnits (Float.Model.magnitude n))) :=
      signedNot (Float.Model.signBit n) (Float.Theory.magUnits (Float.Model.magnitude n))
    _ = Int.neg (Float.Model.units n) := Eq.cong Int.neg (Float.Theory.unitsMag n).flipped
  J (b w => Float.Model.units b = Int.neg (Float.Model.units n)) flip (Float.Theory.negBits x nx).flipped

theorem intOfNonneg ∀ (a: Int) (h: Int.leq (OfNat 0) a = True): a = OfNat (Int.natAbs a) := arithmetic [h]

theorem natOfIntBelow ∀ (u: Int) (wd k: Nat) (eu: u = OfNat wd) (h: Int.leq u (OfNat k) = True): wd ≤ k :=
  arithmetic [eu, h]

theorem natOfIntAbove ∀ (lo u: Int) (m wd: Nat)
    (h1: Int.leq (OfNat m) lo = True)
    (h2: Int.leq lo u = True)
    (eu: u = OfNat wd):
    m ≤ wd :=
  arithmetic [h1, h2, eu]

theorem shareFinal ∀ (ur uw: Int) (r wd v e: Nat)
    (er: ur = OfNat r)
    (ew: uw = OfNat wd)
    (ee: e = v * 4096)
    (g: r + v * 4096 ≤ wd):
    Int.leq (Int.add ur (OfNat e)) uw = True :=
  arithmetic [er, ew, ee, g]

theorem scaleLeft ∀ (r v m: Nat): r * (v * m) * m = r * (m * m) * v := algebra

theorem scaleRight ∀ (wd v k m h: Nat): v * k * wd * m + (v * k * wd + v * m * h) = (wd * (k * m + k) + m * h) * v :=
  algebra

theorem shareGap ∀ (r wd v: Nat)
    (pv: 1 ≤ v)
    (scaled: r * (9007199254740992 * 9007199254740992)
      ≤ wd * (7656119366529843 * 9007199254740992 + 7656119366529843) + 9007199254740992 * 4503599627370496)
    (big: v * 90071 ≤ wd):
    r + v * 4096 ≤ wd :=
  arithmetic [pv, scaled, big]

theorem absDiffBelow ∀ (a b m c: Nat) (h: Nat.absDiff a b * m ≤ c): a * m ≤ b * m + c :=
  let d: Nat := Nat.absDiff a b
  let s: a * m ≤ (b + d) * m := Nat.leMulRight a (b + d) m (arithmetic)
  let e: (b + d) * m = b * m + d * m := algebra
  arithmetic [s, e, h]

theorem shareErrorScaled ∀ (r wd v k m h: Nat)
    (pv: 0 < v)
    (err: Nat.absDiff (r * (v * m)) (v * k * wd) * m ≤ v * k * wd + v * m * h):
    r * (m * m) ≤ wd * (k * m + k) + m * h :=
  let a: r * (v * m) * m ≤ v * k * wd * m + (v * k * wd + v * m * h) :=
    absDiffBelow (r * (v * m)) (v * k * wd) m (v * k * wd + v * m * h) err
  let b: r * (m * m) * v ≤ (wd * (k * m + k) + m * h) * v :=
    rewrite (scaleLeft r v m).flipped, (scaleRight wd v k m h).flipped then a
  Float.Theory.cancelLe (r * (m * m)) (wd * (k * m + k) + m * h) v pv b

theorem intMulOfNat ∀ (a b: Nat): Int.mul (OfNat a) (OfNat b) = OfNat (a * b) := algebra

theorem posOfOne ∀ (v: Nat) (h: 1 ≤ v): 0 < v := arithmetic [h]

theorem shareAboveAt ∀ (width: Float) (v e: Nat)
    (pv: 1 ≤ v)
    (u85: Float.Theory.units 0.85 = OfNat (v * 7656119366529843))
    (u180: Float.Theory.units 180.0 = OfNat (v * 1621295865853378560))
    (u1e11: Int.leq (OfNat (v * 90071)) (Float.Theory.units 1e-11) = True)
    (p1074: Float.Model.pow2 1074 = v * 9007199254740992)
    (top: v * 1621295865853378560 * (v * 7656119366529843) < Float.Model.pow2 1074 * Nat.pow 2 2097)
    (ee: e = v * 4096)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0):
    Int.leq (Int.add (Float.Theory.units (0.85 * width)) (OfNat e)) (Float.Theory.units width) = True :=
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := floatLeTrans 0.0 1e-11 width byComputing wLo
  let r: Float := 0.85 * width
  let sr := shareOfWidth 0.85 width byComputing byComputing fw w0
  let wd: Nat := Int.natAbs (Float.Theory.units width)
  let rn: Nat := Int.natAbs (Float.Theory.units r)
  let wu: Float.Theory.units width = OfNat wd :=
    intOfNonneg (Float.Theory.units width) (Float.Theory.unitsNonneg width w0)
  let ru: Float.Theory.units r = OfNat rn :=
    intOfNonneg (Float.Theory.units r) (Float.Theory.unitsNonneg r sr.right.left)
  let prod: Int.mul (Float.Theory.units 0.85) (Float.Theory.units width) = OfNat (v * 7656119366529843 * wd) :=
    Eq.trans (Eq.cong2 Int.mul u85 wu) (intMulOfNat (v * 7656119366529843) wd)
  let nAbs: Int.natAbs (Int.mul (Float.Theory.units 0.85) (Float.Theory.units width)) = v * 7656119366529843 * wd :=
    Eq.cong Int.natAbs prod
  let wdTop: wd ≤ v * 1621295865853378560 :=
    natOfIntBelow
      (Float.Theory.units width)
      wd
      (v * 1621295865853378560)
      wu
      (J
        (y z => Int.leq (Float.Theory.units width) y = True)
        (Float.Theory.unitsMonoKey width.bits 180.0.bits wHi)
        u180)
  let prodTop: v * 7656119366529843 * wd ≤ v * 1621295865853378560 * (v * 7656119366529843) :=
    J
      (y z => y ≤ v * 1621295865853378560 * (v * 7656119366529843))
      (Nat.leMulRight wd (v * 1621295865853378560) (v * 7656119366529843) wdTop)
      (Nat.mulComm wd (v * 7656119366529843))
  let small: Int.natAbs (Int.mul (Float.Theory.units 0.85) (Float.Theory.units width))
    < Float.Model.pow2 1074 * Nat.pow 2 2097 :=
    J
      (y z => y < Float.Model.pow2 1074 * Nat.pow 2 2097)
      (Float.Theory.leLessTrans
        (v * 7656119366529843 * wd)
        (v * 1621295865853378560 * (v * 7656119366529843))
        (Float.Model.pow2 1074 * Nat.pow 2 2097)
        prodTop
        top)
      nAbs.flipped
  let err := Float.mulRelError 0.85 width byComputing fw sr.left small
  let err1: Nat.absDiff (rn * Float.Model.pow2 1074) (v * 7656119366529843 * wd) * 9007199254740992
    ≤ v * 7656119366529843 * wd + Float.Model.pow2 1074 * 4503599627370496 :=
    rewrite nAbs at err then err
  let err2: Nat.absDiff (rn * (v * 9007199254740992)) (v * 7656119366529843 * wd) * 9007199254740992
    ≤ v * 7656119366529843 * wd + v * 9007199254740992 * 4503599627370496 :=
    J
      (y z =>
        Nat.absDiff (rn * y) (v * 7656119366529843 * wd) * 9007199254740992
          ≤ v * 7656119366529843 * wd + y * 4503599627370496)
      err1
      p1074
  let big: v * 90071 ≤ wd :=
    natOfIntAbove
      (Float.Theory.units 1e-11)
      (Float.Theory.units width)
      (v * 90071)
      wd
      u1e11
      (Float.Theory.unitsMonoKey 1e-11.bits width.bits wLo)
      wu
  let gap :=
    shareGap rn wd v pv
      (shareErrorScaled rn wd v 7656119366529843 9007199254740992 4503599627370496 (posOfOne v pv) err2)
      big
  shareFinal (Float.Theory.units r) (Float.Theory.units width) rn wd v e ru wu ee gap

--| `0.85 * width` is at least 8 · 2^-44 below `width`, in exact units, for
--| a width from 1e-11° to 180°: the standard model for `*` puts it within
--| 2^-53 of 0.85 of the width, and 0.15 of 1e-11° is over 8 · 2^-44.

--| `0.85 * width` is at least 8 · 2^-44 below `width`, in exact units, for
--| a width from 1e-11° to 180°: the standard model for `*` puts it within
--| 2^-53 of 0.85 of the width, and 0.15 of 1e-11° is over 8 · 2^-44.
theorem shareAbove ∀ (width: Float)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0):
    Int.leq (Int.add (Float.Theory.units (0.85 * width)) (OfNat (Float.Model.pow2 1030 * 8))) (Float.Theory.units width)
      = True :=
  shareAboveAt width
    (Float.Model.pow2 1021)
    (Float.Model.pow2 1030 * 8)
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    wLo
    wHi

theorem marginUpArith ∀ (l dd rr c wd t2 t: Int) (w e: Nat)
    (ee: e = w * 4)
    (dn: dd = Int.neg rr)
    (core: Int.leq (Int.add rr (OfNat (w * 8))) wd = True)
    (s1: Int.leq (Int.add l dd) (Int.add c (OfNat (w * 2))) = True)
    (s2: Int.leq (Int.add c wd) (Int.add t2 (OfNat (w * 2))) = True)
    (mono: Int.leq t2 t = True):
    Int.leq (Int.add l (OfNat e)) t = True :=
  arithmetic [ee, dn, core, s1, s2, mono]

--| A share of the width negated: from -180° to -0.
theorem negShare ∀ (a width: Float)
    (fa: Float.isFinite (a * width) = True)
    (low: 0.0 <= a * width)
    (high: a * width <= width)
    (wHi: width <= 180.0):
    (Float.isNaN (a * width) = False) ∧ ((-180.0 <= -(a * width)) ∧ (-(a * width) <= -0.0)) :=
  let n: Float.isNaN (a * width) = False :=
    Float.Theory.finiteNotNaN (a * width).bits (Float.Theory.finiteBits (a * width) fa)
  Both n
    (Both
      (Float.negAntitone (a * width) 180.0 n byComputing (floatLeTrans (a * width) width 180.0 high wHi))
      (Float.negAntitone 0.0 (a * width) byComputing n low))

--| The exact margin at the upper edge: for a band from 1e-11° to 180° wide
--| around `lat` within 180°, the unrounded upper edge `from + width` is at
--| least 2^-42 above the answer, in exact units, so `ceilTo`'s error at
--| step 0.1 (`ceilToTenthBound`) can't carry it below the answer.
--|
--| The proof: `from` is at least `lat - 0.85 * width` (`marginRow`), so
--| `from + width` is at least `(lat - 0.85 * width) + width`, which the
--| standard model for `+` (`sumNear`, twice) puts within 2^-42 of
--| `lat + (width - 0.85 * width)`, and `shareAbove` puts the bracket over
--| 8 · 2^-44.
theorem marginAboveExact ∀ (lat width unit: Float)
    (latLo: -180.0 <= lat)
    (latHi: lat <= 180.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    Int.leq
      (Int.add (Float.Theory.units lat) (OfNat (Float.Model.pow2 1032)))
      (Float.Theory.units (lat - placeAt unit * width + width))
      = True :=
  let fl: Float.isFinite lat = True := Float.finiteBetween (-180.0) lat 180.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := floatLeTrans 0.0 1e-11 width byComputing wLo
  let lLo: -361.0 <= lat := floatLeTrans (-361.0) (-180.0) lat byComputing latLo
  let lHi: lat <= 361.0 := floatLeTrans lat 180.0 361.0 latHi byComputing
  let row := marginRow lat width unit fl fw w0 low high
  let fr: Float := lat - placeAt unit * width
  let r: Float := 0.85 * width
  let sr := shareOfWidth 0.85 width byComputing byComputing fw w0
  let nr := negShare 0.85 width sr.left sr.right.left sr.right.right wHi
  let d: Float := -r
  let fd: Float.isFinite d = True :=
    Float.finiteBetween (-180.0) d (-0.0) byComputing byComputing nr.right.left nr.right.right
  let dLo: -361.0 <= d := floatLeTrans (-361.0) (-180.0) d byComputing nr.right.left
  let dHi: d <= 361.0 := floatLeTrans d (-0.0) 361.0 nr.right.right byComputing
  let s1 := sumNear lat d lLo lHi dLo dHi
  let c: Float := lat + d
  let cLo: -361.0 <= c :=
    floatLeTrans
      (-361.0)
      (-180.0 + -180.0)
      c
      byComputing
      (floatLeTrans
        (-180.0 + -180.0)
        (-180.0 + d)
        c
        (Float.addMonotone (-180.0) d (-180.0) byComputing fd byComputing nr.right.left)
        (Float.addMonotoneLeft (-180.0) lat d byComputing fl fd latLo))
  let cHi: c <= 361.0 :=
    floatLeTrans c
      (180.0 + -0.0)
      361.0
      (floatLeTrans c
        (180.0 + d)
        (180.0 + -0.0)
        (Float.addMonotoneLeft lat 180.0 d fl byComputing fd latHi)
        (Float.addMonotone d (-0.0) 180.0 fd byComputing byComputing nr.right.right))
      byComputing
  let e: lat - r = lat + d := Float.subAddNeg lat r
  let cfr: c <= fr := J (y z => y <= fr) row.left e
  let q: Float := 0.15 * width
  let sq := shareOfWidth 0.15 width byComputing byComputing fw w0
  let nq := negShare 0.15 width sq.left sq.right.left sq.right.right wHi
  let s0 :=
    sumNear lat
      (-q)
      lLo
      lHi
      (floatLeTrans (-361.0) (-180.0) (-q) byComputing nq.right.left)
      (floatLeTrans (-q) (-0.0) 361.0 nq.right.right byComputing)
  let fUpper: Float.isFinite (lat - q) = True :=
    J (y z => Float.isFinite y = True) s0.left (Float.subAddNeg lat q).flipped
  let ffr: Float.isFinite fr = True := Float.finiteBetween c fr (lat - q) s1.left fUpper cfr row.right
  let t1: c + width <= fr + width := Float.addMonotoneLeft c fr width s1.left ffr fw cfr
  let s2 :=
    sumNear c width cLo cHi
      (floatLeTrans (-361.0) 0.0 width byComputing w0)
      (floatLeTrans width 180.0 361.0 wHi byComputing)
  marginUpArith
    (Float.Theory.units lat)
    (Float.Theory.units d)
    (Float.Theory.units r)
    (Float.Theory.units c)
    (Float.Theory.units width)
    (Float.Theory.units (c + width))
    (Float.Theory.units (fr + width))
    (Float.Model.pow2 1030)
    (Float.Model.pow2 1032)
    byComputing
    (unitsNeg r nr.left)
    (shareAbove width wLo wHi)
    s1.right.left
    s2.right.left
    (Float.Theory.unitsMonoKey (c + width).bits (fr + width).bits t1)
