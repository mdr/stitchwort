--| What is proved about hint bands, and what is settled by computing.
--| std's float laws (std/Float/Theory.sw) cover `seededUnit`; NOTES.md
--| lists the laws the other band theorems still need.

namespace Whereabouts.Hints.Proofs
import Whereabouts.Hints (..)
import Std (Bool, Eq, Float, Int, List, Nat, Ord, Void)

--| mulberry32's last word is a word.
theorem finalWordBelow ∀ (parts: List Float): finalWord parts < 4294967296 :=
  Nat.modLt (Nat.xor (mix parts) (Nat.shiftRight (mix parts) 14)) 4294967296

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
  let abs360: Int.natAbs (Float.Theory.units 360.0) = p * 360 := byComputing
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
    J (k w => Int.natAbs (Float.Theory.units u) < k) ru.right abs360
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
        (J (k z => Int.natAbs (Float.Theory.units w) < k) rw.right abs360))
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

--| `describeHint`'s rounding to tenths leaves every tenth up to 360.1° in
--| size as it is, so the label of an edge that is a tenth is that edge.
--| (`labelRound`: `/ 10.0` and `* 10.0` stay well within half a unit of
--| the whole number.)
theorem tenthsKeepTheirLabel ∀ (r: Int) (h: Int.natAbs r ≤ 3601): Float.round (tenth r * 10.0) / 10.0 = tenth r :=
  let k: Float := wholeAt r False
  let f := wholeAtFacts r False (tenthsSizeSmall r h)
  Float.Theory.orCase
    [goal := Float.round (k / 10.0 * 10.0) / 10.0 = k / 10.0]
    (Float.Theory.intZeroCases r)
    (r0 =>
      J (y w => Float.round (wholeAt y False / 10.0 * 10.0) / 10.0 = wholeAt y False / 10.0) byComputing r0.flipped)
    (nz => Eq.cong (y => y / 10.0) (labelRound k r f.left f.right nz h))

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
  let atLow: 0.0 <= at := Float.Theory.leTrans 0.0 0.15 at byComputing r.left
  let atHigh: at <= 1.0 := Float.Theory.leTrans at 0.85 1.0 r.right byComputing
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

--| What holds for each whole number `k` of tenths (`tenthsAt`): the round trip; that
--| `tenthsSlack` below its tenth divides by 0.1 to below `k`, and above it
--| to above `k`; and that the tenth is within 361°.
def tenthsCheck (k: Float): Bool :=
  let whole := Float.round (k * 0.1 * 10.0)
  let t := whole / 10.0
  Nat.equal whole.bits k.bits
    ∧ (Float.less ((t - tenthsSlack) / 0.1) k
      ∧ (Float.less k ((t + tenthsSlack) / 0.1) ∧ (Float.leq (-361.0) t ∧ Float.leq t 361.0)))

theorem wholeAtValid ∀ (i: Int) (s: Bool): Float.isValid (Float.Model.roundScaled i 0 s) = True :=
  Float.Theory.roundRatioValid 1 (OfNat 0) s byComputing i

theorem wholeAtOf ∀ (k: Float) (i: Int) (s: Bool) (e: k.bits = Float.Model.roundScaled i 0 s): k = wholeAt i s :=
  Float.bitsExt k
    (wholeAt i s)
    (Eq.trans e (Float.Theory.ofBitsBits (Float.Model.roundScaled i 0 s) (wholeAtValid i s)).flipped)

theorem yUp ∀ (y b: Nat)
    (y1: y * 9007199254740992 ≤ b * 3602879701896397 * 9007199254740992 + b * 3602879701896397 + 4503599627370496):
    y ≤ b * 3602879701896397 + b + 1 :=
  arithmetic [y1]

theorem yDown ∀ (y b: Nat)
    (y2: b * 3602879701896397 * 9007199254740992 ≤ y * 9007199254740992 + b * 3602879701896397 + 4503599627370496):
    b * 3602879701896397 ≤ y + b + 1 :=
  arithmetic [y2]

theorem zUp ∀ (z y b: Nat)
    (yu: y ≤ b * 3602879701896397 + b + 1)
    (z1: z * 9007199254740992 ≤ y * 10 * 9007199254740992 + y * 10 + 4503599627370496):
    z ≤ b * 36028797018963970 + b * 20 + 20 :=
  arithmetic [yu, z1]

theorem zDown ∀ (z y b: Nat)
    (yd: b * 3602879701896397 ≤ y + b + 1)
    (z2: y * 10 * 9007199254740992 ≤ z * 9007199254740992 + y * 10 + 4503599627370496):
    b * 36028797018963970 ≤ z + b * 20 + 20 :=
  arithmetic [yd, z2]

theorem belowTopY ∀ (b v t: Nat) (bv: b ≤ v * 3601) (top: v * 12974069856543025597 < t): b * 3602879701896397 < t :=
  arithmetic [bv, top]

theorem belowTopZ ∀ (y b v t: Nat)
    (yu: y ≤ b * 3602879701896397 + b + 1)
    (bv: b ≤ v * 3601)
    (top: v * 129740698565430256000 + 10 < t):
    y * 10 < t :=
  arithmetic [yu, bv, top]

theorem natAbsOfNat ∀ (a: Nat): Int.natAbs (OfNat a) = a := byComputing

--| The magnitudes in the round trip `k * 0.1 * 10.0`, for `k` of `b · 2^55`
--| units (`b` = |n| · 2^1019): each product within 2^-53 of the exact one,
--| so the result is within `20b + 20` units of `(2^55 + 2) b`.
theorem tripMagnitudes ∀ (k: Float) (b v: Nat)
    (pv: Float.Model.pow2 1074 = v * 36028797018963968)
    (vpos: 0 < v)
    (bv: b ≤ v * 3601)
    (topY: v * 12974069856543025597 < Nat.pow 2 2097)
    (topZ: v * 129740698565430256000 + 10 < Nat.pow 2 2097)
    (u01: Int.natAbs (Float.Theory.units 0.1) = v * 3602879701896397)
    (u10: Float.Theory.units 10.0 = OfNat (v * 360287970189639680))
    (ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968)
    (fk: Float.isFinite k = True)
    (fy: Float.isFinite (k * 0.1) = True)
    (fz: Float.isFinite (k * 0.1 * 10.0) = True):
    (Int.natAbs (Float.Theory.units (k * 0.1 * 10.0)) ≤ b * 36028797018963970 + b * 20 + 20)
      ∧ (b * 36028797018963970 ≤ Int.natAbs (Float.Theory.units (k * 0.1 * 10.0)) + b * 20 + 20) :=
  let p: Nat := Float.Model.pow2 1074
  let pp: 0 < p := byComputing
  let y: Float := k * 0.1
  let yy: Nat := Int.natAbs (Float.Theory.units y)
  let zz: Nat := Int.natAbs (Float.Theory.units (y * 10.0))
  let n1: Int.natAbs (Int.mul (Float.Theory.units k) (Float.Theory.units 0.1)) = b * 3602879701896397 * p :=
    rewrite Int.natAbsMul (Float.Theory.units k) (Float.Theory.units 0.1), ku, u01, pv then algebra
  let s1: Int.natAbs (Int.mul (Float.Theory.units k) (Float.Theory.units 0.1)) < p * Nat.pow 2 2097 :=
    J
      (x w => x < p * Nat.pow 2 2097)
      (J
        (x w => b * 3602879701896397 * p < x)
        (Float.Theory.mulLtRight (b * 3602879701896397) (Nat.pow 2 2097) p (belowTopY b v (Nat.pow 2 2097) bv topY) pp)
        (Nat.mulComm (Nat.pow 2 2097) p))
      n1.flipped
  let e1 := Float.mulRelError k 0.1 fk byComputing fy s1
  let f1: Nat.absDiff (yy * p) (b * 3602879701896397 * p) * 9007199254740992
    ≤ b * 3602879701896397 * p + p * 4503599627370496 :=
    J (x w => Nat.absDiff (yy * p) x * 9007199254740992 ≤ x + p * 4503599627370496) e1 n1
  let y1 := Float.Theory.relCancelUp yy (b * 3602879701896397) p 9007199254740992 4503599627370496 pp f1
  let y2 := Float.Theory.relCancelDown yy (b * 3602879701896397) p 9007199254740992 4503599627370496 pp f1
  let yu := yUp yy b y1
  let yd := yDown yy b y2
  let n2: Int.natAbs (Int.mul (Float.Theory.units y) (Float.Theory.units 10.0)) = yy * 10 * p := calc Int.natAbs
    (Int.mul (Float.Theory.units y) (Float.Theory.units 10.0))
    _ = yy * Int.natAbs (Float.Theory.units 10.0) := Int.natAbsMul (Float.Theory.units y) (Float.Theory.units 10.0)
    _ = yy * (v * 360287970189639680) := Eq.cong (x => yy * Int.natAbs x) u10
    _ = yy * 10 * (v * 36028797018963968) := algebra
    _ = yy * 10 * p := Eq.cong (x => yy * 10 * x) pv.flipped
  let s2: Int.natAbs (Int.mul (Float.Theory.units y) (Float.Theory.units 10.0)) < p * Nat.pow 2 2097 :=
    J
      (x w => x < p * Nat.pow 2 2097)
      (J
        (x w => yy * 10 * p < x)
        (Float.Theory.mulLtRight (yy * 10) (Nat.pow 2 2097) p (belowTopZ yy b v (Nat.pow 2 2097) yu bv topZ) pp)
        (Nat.mulComm (Nat.pow 2 2097) p))
      n2.flipped
  let e2 := Float.mulRelError y 10.0 fy byComputing fz s2
  let f2: Nat.absDiff (zz * p) (yy * 10 * p) * 9007199254740992 ≤ yy * 10 * p + p * 4503599627370496 :=
    J (x w => Nat.absDiff (zz * p) x * 9007199254740992 ≤ x + p * 4503599627370496) e2 n2
  let z1 := Float.Theory.relCancelUp zz (yy * 10) p 9007199254740992 4503599627370496 pp f2
  let z2 := Float.Theory.relCancelDown zz (yy * 10) p 9007199254740992 4503599627370496 pp f2
  Both (zUp zz yy b yu z1) (zDown zz yy b yd z2)

theorem tripNear ∀ (np u: Int) (b z v h p: Nat)
    (en: Int.natAbs np = b * 36028797018963968)
    (eu: Int.natAbs u = z)
    (eh: h = v * 18014398509481984)
    (ep: p = v * 36028797018963968)
    (bv: b ≤ v * 3601)
    (v1: 1 ≤ v)
    (zu: z ≤ b * 36028797018963970 + b * 20 + 20)
    (zd: b * 36028797018963970 ≤ z + b * 20 + 20)
    (sign: ((Int.leq (OfNat 0) np = True) ∧ (Int.leq (OfNat 0) u = True))
      ∨ ((Int.less np (OfNat 0) = True) ∧ (Int.leq u (OfNat 0) = True))):
    (Int.leq np (Int.add u (OfNat h)) = True) ∧ (Int.less (Int.add u (OfNat h)) (Int.add np (OfNat p)) = True) :=
  match sign with
    | Inl s =>
      let s1 := s.left
      let s2 := s.right
      Both (arithmetic [en, eu, eh, ep, bv, v1, zu, zd, s1, s2]) (arithmetic [en, eu, eh, ep, bv, v1, zu, zd, s1, s2])
    | Inr s =>
      let s1 := s.left
      let s2 := s.right
      Both (arithmetic [en, eu, eh, ep, bv, v1, zu, zd, s1, s2]) (arithmetic [en, eu, eh, ep, bv, v1, zu, zd, s1, s2])

theorem posOfNonzero ∀ (u: Int) (h: Int.leq (OfNat 0) u = True) (nz: u ≠ OfNat 0): Int.less (OfNat 0) u = True :=
  arithmetic [h, nz]

theorem scaledBound ∀ (m v: Nat) (h: m ≤ 3601): m * v ≤ v * 3601 :=
  J (y w => m * v ≤ y) (Nat.leMulRight m 3601 v h) (Nat.mulComm 3601 v)

theorem kBelowTop ∀ (u: Int) (b v: Nat)
    (ku: Int.natAbs u = b * 36028797018963968)
    (bv: b ≤ v * 3601)
    (v1: 1 ≤ v):
    (Int.less u (OfNat (v * 129775726862308212736)) = True)
      ∧ (Int.less (Int.neg (OfNat (v * 129775726862308212736))) u = True) :=
  Both (arithmetic [ku, bv, v1]) (arithmetic [ku, bv, v1])

--| `tripNonzero` once the signs are known: `tripMagnitudes` puts the result
--| within `20b + 20` units of `(2^55 + 2) b`, under half a unit from `n`
--| (`tripNear`), and `roundNear` finds `n`.
theorem tripFinish ∀ (k: Float) (n: Int) (b: Nat)
    (fk: Float.isFinite k = True)
    (whole: Float.Theory.units k = Int.mul n (OfNat (Float.Model.pow2 1074)))
    (nz: n ≠ OfNat 0)
    (bv: b ≤ Float.Model.pow2 1019 * 3601)
    (ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968)
    (fy: Float.isFinite (k * 0.1) = True)
    (fz: Float.isFinite (k * 0.1 * 10.0) = True)
    (sign: ((Int.leq (OfNat 0) (Float.Theory.units k) = True)
      ∧ (Int.leq (OfNat 0) (Float.Theory.units (k * 0.1 * 10.0)) = True))
      ∨ ((Int.less (Float.Theory.units k) (OfNat 0) = True)
        ∧ (Int.leq (Float.Theory.units (k * 0.1 * 10.0)) (OfNat 0) = True))):
    Float.round (k * 0.1 * 10.0) = k :=
  let p: Nat := Float.Model.pow2 1074
  let v: Nat := Float.Model.pow2 1019
  let pv: Float.Model.pow2 1074 = Float.Model.pow2 1019 * 36028797018963968 := byComputing
  let z: Float := k * 0.1 * 10.0
  let mags := tripMagnitudes k b v pv byComputing bv byComputing byComputing byComputing byComputing ku fk fy fz
  let near :=
    tripNear
      (Float.Theory.units k)
      (Float.Theory.units z)
      b
      (Int.natAbs (Float.Theory.units z))
      v
      (Float.Model.pow2 1073)
      p
      ku
      byComputing
      byComputing
      pv
      bv
      byComputing
      mags.left
      mags.right
      sign
  Float.roundNear z k n fz fk whole nz
    (J (y w => Int.leq y (Int.add (Float.Theory.units z) (OfNat (Float.Model.pow2 1073))) = True) near.left whole)
    (J
      (y w => Int.less (Int.add (Float.Theory.units z) (OfNat (Float.Model.pow2 1073))) (Int.add y (OfNat p)) = True)
      near.right
      whole)

--| The round trip `round (k * 0.1 * 10.0) = k` for a whole double `k` of a
--| nonzero `n` up to 3601 in size: the standard model for `*`, twice, puts
--| `k * 0.1 * 10.0` well within half a unit of `n`, and `round` finds `n`.
theorem tripNonzero ∀ (k: Float) (n: Int)
    (fk: Float.isFinite k = True)
    (whole: Float.Theory.units k = Int.mul n (OfNat (Float.Model.pow2 1074)))
    (nz: n ≠ OfNat 0)
    (h: Int.natAbs n ≤ 3601):
    Float.round (k * 0.1 * 10.0) = k :=
  let p: Nat := Float.Model.pow2 1074
  let v: Nat := Float.Model.pow2 1019
  let v1: 1 ≤ v := byComputing
  let m: Nat := Int.natAbs n
  let b: Nat := m * v
  let bv: b ≤ v * 3601 := scaledBound m v h
  let np: Int := Int.mul n (OfNat p)
  let ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968 := calc Int.natAbs (Float.Theory.units k)
    _ = Int.natAbs np := Eq.cong Int.natAbs whole
    _ = m * p := Int.natAbsMul n (OfNat p)
    _ = m * (v * 36028797018963968) :=
      Eq.cong (x => m * x) (byComputing: Float.Model.pow2 1074 = Float.Model.pow2 1019 * 36028797018963968)
    _ = b * 36028797018963968 := algebra
  let top := kBelowTop (Float.Theory.units k) b v ku bv v1
  let z: Float := k * 0.1 * 10.0
  Float.Theory.orCase
    [goal := Float.round (k * 0.1 * 10.0) = k]
    (Float.Theory.boolCases (Int.leq (OfNat 0) (Float.Theory.units k)))
    (nonneg =>
      let pos: Int.less (Float.Theory.units 0.0) (Float.Theory.units k) = True :=
        J
          (y w => Int.less y (Float.Theory.units k) = True)
          (posOfNonzero
            (Float.Theory.units k)
            nonneg
            (J (y w => y ≠ OfNat 0) (Float.Theory.mulNonzero n p byComputing nz) whole.flipped))
          (byComputing: OfNat 0 = Float.Theory.units 0.0)
      let lo: 0.0 <= k := floatLeOfLt 0.0 k (Float.Theory.lessOfUnits 0.0 k pos)
      let hi: k <= 3602.0 :=
        floatLeOfLt k 3602.0
          (Float.Theory.lessOfUnits k 3602.0
            (J
              (y w => Int.less (Float.Theory.units k) y = True)
              top.left
              (byComputing: OfNat (v * 129775726862308212736) = Float.Theory.units 3602.0)))
      let s1 :=
        Float.mulBetween 0.0 k 3602.0 0.1 byComputing byComputing fk byComputing byComputing byComputing byComputing lo
            hi
      let s2 :=
        Float.mulBetween
          (0.0 * 0.1)
          (k * 0.1)
          (3602.0 * 0.1)
          10.0
          byComputing
          byComputing
          s1.left
          byComputing
          byComputing
          byComputing
          byComputing
          s1.right.left
          s1.right.right
      let z0: 0.0 <= z := J (y w => y <= z) s2.right.left (byComputing: 0.0 * 0.1 * 10.0 = 0.0)
      tripFinish k n b fk whole nz bv ku s1.left s2.left (Inl (Both nonneg (Float.Theory.unitsNonneg z z0))))
    (notNonneg =>
      let neg: Int.less (Float.Theory.units k) (OfNat 0) = True :=
        Float.Theory.intLessZeroOfNotNonneg (Float.Theory.units k) notNonneg
      let hi: k <= -0.0 :=
        floatLeOfLt k
          (-0.0)
          (Float.Theory.lessOfUnits k
            (-0.0)
            (J
              (y w => Int.less (Float.Theory.units k) y = True)
              neg
              (byComputing: OfNat 0 = Float.Theory.units (-0.0))))
      let lo: -3602.0 <= k :=
        floatLeOfLt
          (-3602.0)
          k
          (Float.Theory.lessOfUnits
            (-3602.0)
            k
            (J
              (y w => Int.less y (Float.Theory.units k) = True)
              top.right
              (byComputing: Int.neg (OfNat (v * 129775726862308212736)) = Float.Theory.units (-3602.0))))
      let s1 :=
        Float.mulBetween
          (-3602.0)
          k
          (-0.0)
          0.1
          byComputing
          byComputing
          fk
          byComputing
          byComputing
          byComputing
          byComputing
          lo
          hi
      let s2 :=
        Float.mulBetween
          (-3602.0 * 0.1)
          (k * 0.1)
          (-0.0 * 0.1)
          10.0
          byComputing
          byComputing
          s1.left
          byComputing
          byComputing
          byComputing
          byComputing
          s1.right.left
          s1.right.right
      let zle: z <= -0.0 := J (y w => z <= y) s2.right.right (byComputing: -0.0 * 0.1 * 10.0 = -0.0)
      tripFinish k n b fk whole nz bv ku s1.left s2.left
        (Inr
          (Both neg
            (J
              (y w => Int.leq (Float.Theory.units z) y = True)
              (Float.Theory.unitsMonoKey z.bits (-0.0).bits zle)
              (byComputing: Float.Theory.units (-0.0) = OfNat 0)))))

theorem slackBelowPos ∀ (k t c q d: Int) (b v tt cc qq w: Nat)
    (kAbs: Int.natAbs k = b * 36028797018963968)
    (bv: b ≤ v * 3601)
    (v1: 1 ≤ v)
    (kPos: Int.less (OfNat 0) k = True)
    (tPos: Int.leq (OfNat 0) t = True)
    (cPos: Int.leq (OfNat 0) c = True)
    (qPos: Int.leq (OfNat 0) q = True)
    (et: Int.natAbs t = tt)
    (ec: Int.natAbs c = cc)
    (eq: Int.natAbs q = qq)
    (t1: tt * 10 ≤ b * 36028797018963968 + v * 14404 + 5)
    (ed: d = Int.neg (OfNat (v * 6144)))
    (ew: w = v * 2048)
    (s2: Int.leq c (Int.add (Int.add t d) (OfNat w)) = True)
    (q1: qq * 3602879701896397 ≤ cc * 36028797018963972 + 3602879701896397):
    Int.less q k = True :=
  arithmetic [kAbs, bv, v1, kPos, tPos, cPos, qPos, et, ec, eq, t1, ed, ew, s2, q1]

theorem slackAbovePos ∀ (k t c q d: Int) (b v tt cc qq w: Nat)
    (kAbs: Int.natAbs k = b * 36028797018963968)
    (bv: b ≤ v * 3601)
    (v1: 1 ≤ v)
    (kPos: Int.less (OfNat 0) k = True)
    (tPos: Int.leq (OfNat 0) t = True)
    (cPos: Int.leq (OfNat 0) c = True)
    (qPos: Int.leq (OfNat 0) q = True)
    (et: Int.natAbs t = tt)
    (ec: Int.natAbs c = cc)
    (eq: Int.natAbs q = qq)
    (t2: b * 36028797018963968 ≤ tt * 10 + v * 14404 + 5)
    (ed: d = OfNat (v * 6144))
    (ew: w = v * 2048)
    (s1: Int.leq (Int.add t d) (Int.add c (OfNat w)) = True)
    (q2: cc * 36028797018963964 ≤ qq * 3602879701896397 + 3602879701896397):
    Int.less k q = True :=
  arithmetic [kAbs, bv, v1, kPos, tPos, cPos, qPos, et, ec, eq, t2, ed, ew, s1, q2]

theorem slackBelowNeg ∀ (k t c q d: Int) (b v tt cc qq w: Nat)
    (kAbs: Int.natAbs k = b * 36028797018963968)
    (bv: b ≤ v * 3601)
    (v1: 1 ≤ v)
    (kNeg: Int.less k (OfNat 0) = True)
    (tNeg: Int.leq t (OfNat 0) = True)
    (cNeg: Int.leq c (OfNat 0) = True)
    (qNeg: Int.leq q (OfNat 0) = True)
    (et: Int.natAbs t = tt)
    (ec: Int.natAbs c = cc)
    (eq: Int.natAbs q = qq)
    (t2: b * 36028797018963968 ≤ tt * 10 + v * 14404 + 5)
    (ed: d = Int.neg (OfNat (v * 6144)))
    (ew: w = v * 2048)
    (s2: Int.leq c (Int.add (Int.add t d) (OfNat w)) = True)
    (q2: cc * 36028797018963964 ≤ qq * 3602879701896397 + 3602879701896397):
    Int.less q k = True :=
  arithmetic [kAbs, bv, v1, kNeg, tNeg, cNeg, qNeg, et, ec, eq, t2, ed, ew, s2, q2]

theorem slackAboveNeg ∀ (k t c q d: Int) (b v tt cc qq w: Nat)
    (kAbs: Int.natAbs k = b * 36028797018963968)
    (bv: b ≤ v * 3601)
    (v1: 1 ≤ v)
    (kNeg: Int.less k (OfNat 0) = True)
    (tNeg: Int.leq t (OfNat 0) = True)
    (cNeg: Int.leq c (OfNat 0) = True)
    (qNeg: Int.leq q (OfNat 0) = True)
    (et: Int.natAbs t = tt)
    (ec: Int.natAbs c = cc)
    (eq: Int.natAbs q = qq)
    (t1: tt * 10 ≤ b * 36028797018963968 + v * 14404 + 5)
    (ed: d = OfNat (v * 6144))
    (ew: w = v * 2048)
    (s1: Int.leq (Int.add t d) (Int.add c (OfNat w)) = True)
    (q1: qq * 3602879701896397 ≤ cc * 36028797018963972 + 3602879701896397):
    Int.less k q = True :=
  arithmetic [kAbs, bv, v1, kNeg, tNeg, cNeg, qNeg, et, ec, eq, t1, ed, ew, s1, q1]

theorem tenthCoarseArith ∀ (tt b v: Nat)
    (bv: b ≤ v * 3601)
    (up: tt * 10 * 9007199254740992
      ≤ b * 36028797018963968 * 9007199254740992 + b * 36028797018963968 + 45035996273704960)
    (down: b * 36028797018963968 * 9007199254740992
      ≤ tt * 10 * 9007199254740992 + b * 36028797018963968 + 45035996273704960):
    (tt * 10 ≤ b * 36028797018963968 + v * 14404 + 5) ∧ (b * 36028797018963968 ≤ tt * 10 + v * 14404 + 5) :=
  Both (arithmetic [bv, up]) (arithmetic [bv, down])

theorem quotientCoarseArith ∀ (qq cc: Nat)
    (up: qq * 3602879701896397 * 9007199254740992
      ≤ cc * 36028797018963968 * 9007199254740992 + cc * 36028797018963968 + 16225927682921337239877726502912)
    (down: cc * 36028797018963968 * 9007199254740992
      ≤ qq * 3602879701896397 * 9007199254740992 + cc * 36028797018963968 + 16225927682921337239877726502912):
    (qq * 3602879701896397 ≤ cc * 36028797018963972 + 3602879701896397)
      ∧ (cc * 36028797018963964 ≤ qq * 3602879701896397 + 3602879701896397) :=
  Both (arithmetic [up]) (arithmetic [down])

theorem scaledTop ∀ (x b v: Nat) (e: x = b * 36028797018963968) (bv: b ≤ v * 3601): x ≤ v * 129739698065289248768 :=
  arithmetic [e, bv]

theorem natAbsWithin ∀ (u lo hi: Int) (bound: Nat)
    (el: lo = Int.neg (OfNat bound))
    (eh: hi = OfNat bound)
    (a: Int.leq lo u = True)
    (b: Int.leq u hi = True):
    Int.natAbs u ≤ bound :=
  arithmetic [el, eh, a, b]

--| `k / 10.0` within the standard model, for `k` of `b · 2^55` units of
--| 2^-1074: ten times the quotient's units are within `14404 · 2^1019 + 5`
--| of `k`'s. `divRelError`, with 2^1074 cancelled (`relCancel`) and the
--| relative error bounded by `|k| ≤ 3601`.
theorem tenthCoarse ∀ (k: Float) (b: Nat)
    (bv: b ≤ Float.Model.pow2 1019 * 3601)
    (ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968)
    (fk: Float.isFinite k = True)
    (ft: Float.isFinite (k / 10.0) = True):
    (Int.natAbs (Float.Theory.units (k / 10.0)) * 10 ≤ b * 36028797018963968 + Float.Model.pow2 1019 * 14404 + 5)
      ∧ (b * 36028797018963968 ≤ Int.natAbs (Float.Theory.units (k / 10.0)) * 10 + Float.Model.pow2 1019 * 14404 + 5) :=
  let tt: Nat := Int.natAbs (Float.Theory.units (k / 10.0))
  let kk: Nat := Int.natAbs (Float.Theory.units k)
  let top: kk ≤ Float.Model.pow2 1019 * 129739698065289248768 := scaledTop kk b (Float.Model.pow2 1019) ku bv
  let small: kk * Float.Model.pow2 1074 < Int.natAbs (Float.Theory.units 10.0) * Nat.pow 2 2097 :=
    Float.Theory.leLessTrans
      (kk * Float.Model.pow2 1074)
      (Float.Model.pow2 1019 * 129739698065289248768 * Float.Model.pow2 1074)
      (Int.natAbs (Float.Theory.units 10.0) * Nat.pow 2 2097)
      (Nat.leMulRight kk (Float.Model.pow2 1019 * 129739698065289248768) (Float.Model.pow2 1074) top)
      byComputing
  let err := Float.divRelError k 10.0 byComputing byComputing fk ft small
  let two :=
    Float.Theory.relCancel
      (tt * 10)
      (b * 36028797018963968)
      (Float.Model.pow2 1074)
      9007199254740992
      45035996273704960
      (tt * Int.natAbs (Float.Theory.units 10.0))
      (kk * Float.Model.pow2 1074)
      (Int.natAbs (Float.Theory.units 10.0) * 4503599627370496)
      byComputing
      (rewrite (byComputing: Int.natAbs (Float.Theory.units 10.0) = Float.Model.pow2 1074 * 10) then algebra)
      (rewrite ku)
      byComputing
      err
  tenthCoarseArith tt b (Float.Model.pow2 1019) bv two.left two.right

--| `c / 0.1` within the standard model, for `c` within 362°: the quotient's
--| units times 0.1's significand are within `4 |c| + 0.1's significand` of
--| `c`'s units times 2^55. `divRelError`, with 2^1019 cancelled.
theorem quotientCoarse ∀ (c: Float)
    (lo: -362.0 <= c)
    (hi: c <= 362.0)
    (fq: Float.isFinite (c / 0.1) = True):
    (Int.natAbs (Float.Theory.units (c / 0.1)) * 3602879701896397
      ≤ Int.natAbs (Float.Theory.units c) * 36028797018963972 + 3602879701896397)
      ∧ (Int.natAbs (Float.Theory.units c) * 36028797018963964
        ≤ Int.natAbs (Float.Theory.units (c / 0.1)) * 3602879701896397 + 3602879701896397) :=
  let qq: Nat := Int.natAbs (Float.Theory.units (c / 0.1))
  let cc: Nat := Int.natAbs (Float.Theory.units c)
  let fc: Float.isFinite c = True := Float.finiteBetween (-362.0) c 362.0 byComputing byComputing lo hi
  let top: cc ≤ Float.Model.pow2 1019 * 13042424520864956416 :=
    natAbsWithin
      (Float.Theory.units c)
      (Float.Theory.units (-362.0))
      (Float.Theory.units 362.0)
      (Float.Model.pow2 1019 * 13042424520864956416)
      byComputing
      byComputing
      (Float.Theory.unitsMonoKey (-362.0).bits c.bits lo)
      (Float.Theory.unitsMonoKey c.bits 362.0.bits hi)
  let small: cc * Float.Model.pow2 1074 < Int.natAbs (Float.Theory.units 0.1) * Nat.pow 2 2097 :=
    Float.Theory.leLessTrans
      (cc * Float.Model.pow2 1074)
      (Float.Model.pow2 1019 * 13042424520864956416 * Float.Model.pow2 1074)
      (Int.natAbs (Float.Theory.units 0.1) * Nat.pow 2 2097)
      (Nat.leMulRight cc (Float.Model.pow2 1019 * 13042424520864956416) (Float.Model.pow2 1074) top)
      byComputing
  let err := Float.divRelError c 0.1 byComputing byComputing fc fq small
  let two :=
    Float.Theory.relCancel
      (qq * 3602879701896397)
      (cc * 36028797018963968)
      (Float.Model.pow2 1019)
      9007199254740992
      16225927682921337239877726502912
      (qq * Int.natAbs (Float.Theory.units 0.1))
      (cc * Float.Model.pow2 1074)
      (Int.natAbs (Float.Theory.units 0.1) * 4503599627370496)
      byComputing
      (rewrite (byComputing: Int.natAbs (Float.Theory.units 0.1) = Float.Model.pow2 1019 * 3602879701896397) then
        algebra)
      (rewrite (byComputing: Float.Model.pow2 1074 = Float.Model.pow2 1019 * 36028797018963968) then algebra)
      byComputing
      err
  quotientCoarseArith qq cc two.left two.right

theorem atLeastOne ∀ (m v: Nat) (h: 1 ≤ m): v ≤ m * v :=
  J (y w => y ≤ m * v) (Nat.leMulRight 1 m v h) (algebra: 1 * v = v)

theorem nonzeroSize ∀ (i: Int) (nz: i ≠ OfNat 0): 1 ≤ Int.natAbs i := arithmetic [nz]

--| A whole double `k` of `i` has `|i| · 2^1019 · 2^55` units in size.
theorem wholeSize ∀ (k: Float) (i: Int)
    (whole: Float.Theory.units k = Int.mul i (OfNat (Float.Model.pow2 1074))):
    Int.natAbs (Float.Theory.units k) = Int.natAbs i * Float.Model.pow2 1019 * 36028797018963968 :=
  calc Int.natAbs (Float.Theory.units k)
    _ = Int.natAbs (Int.mul i (OfNat (Float.Model.pow2 1074))) := Eq.cong Int.natAbs whole
    _ = Int.natAbs i * Float.Model.pow2 1074 := Int.natAbsMul i (OfNat (Float.Model.pow2 1074))
    _ = Int.natAbs i * (Float.Model.pow2 1019 * 36028797018963968) :=
      Eq.cong (x => Int.natAbs i * x) (byComputing: Float.Model.pow2 1074 = Float.Model.pow2 1019 * 36028797018963968)
    _ = Int.natAbs i * Float.Model.pow2 1019 * 36028797018963968 := algebra

--| `k / 10.0` for a whole `k` up to 3601 in size: finite and within 361°.
theorem tenthSetup ∀ (k: Float) (b: Nat)
    (bv: b ≤ Float.Model.pow2 1019 * 3601)
    (ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968):
    (Float.isFinite (k / 10.0) = True) ∧ ((-361.0 <= k / 10.0) ∧ (k / 10.0 <= 361.0)) :=
  let top := kBelowTop (Float.Theory.units k) b (Float.Model.pow2 1019) ku bv byComputing
  let hi: k <= 3602.0 :=
    floatLeOfLt k 3602.0
      (Float.Theory.lessOfUnits k 3602.0
        (J
          (y w => Int.less (Float.Theory.units k) y = True)
          top.left
          (byComputing: OfNat (Float.Model.pow2 1019 * 129775726862308212736) = Float.Theory.units 3602.0)))
  let lo: -3602.0 <= k :=
    floatLeOfLt
      (-3602.0)
      k
      (Float.Theory.lessOfUnits
        (-3602.0)
        k
        (J
          (y w => Int.less y (Float.Theory.units k) = True)
          top.right
          (byComputing: Int.neg (OfNat (Float.Model.pow2 1019 * 129775726862308212736))
            = Float.Theory.units (-3602.0))))
  let tlo: -3602.0 / 10.0 <= k / 10.0 := Float.divMonotone (-3602.0) k 10.0 byComputing byComputing lo
  let thi: k / 10.0 <= 3602.0 / 10.0 := Float.divMonotone k 3602.0 10.0 byComputing byComputing hi
  Both
    (Float.finiteBetween (-3602.0 / 10.0) (k / 10.0) (3602.0 / 10.0) byComputing byComputing tlo thi)
    (Both
      (Float.Theory.leTrans (-361.0) (-3602.0 / 10.0) (k / 10.0) byComputing tlo)
      (Float.Theory.leTrans (k / 10.0) (3602.0 / 10.0) 361.0 thi byComputing))

--| `t + d` for `t` within 361° and `d` within 1°: within 362°, and its quotient by 0.1 finite.
theorem shiftSetup ∀ (t d: Float)
    (fd: Float.isFinite d = True)
    (lo: -361.0 <= t)
    (hi: t <= 361.0)
    (dlo: -362.0 <= -361.0 + d)
    (dhi: 361.0 + d <= 362.0):
    (Float.isFinite ((t + d) / 0.1) = True) ∧ ((-362.0 <= t + d) ∧ (t + d <= 362.0)) :=
  let ft: Float.isFinite t = True := Float.finiteBetween (-361.0) t 361.0 byComputing byComputing lo hi
  let clo: -362.0 <= t + d :=
    Float.Theory.leTrans (-362.0) (-361.0 + d) (t + d) dlo (Float.addMonotoneLeft (-361.0) t d byComputing ft fd lo)
  let chi: t + d <= 362.0 :=
    Float.Theory.leTrans (t + d) (361.0 + d) 362.0 (Float.addMonotoneLeft t 361.0 d ft byComputing fd hi) dhi
  let qlo: -362.0 / 0.1 <= (t + d) / 0.1 := Float.divMonotone (-362.0) (t + d) 0.1 byComputing byComputing clo
  let qhi: (t + d) / 0.1 <= 362.0 / 0.1 := Float.divMonotone (t + d) 362.0 0.1 byComputing byComputing chi
  Both (Float.finiteBetween (-362.0 / 0.1) ((t + d) / 0.1) (362.0 / 0.1) byComputing byComputing qlo qhi) (Both clo chi)

--| Division by a positive double keeps a positive dividend's sign.
theorem divNonnegUnits ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (z0: 0.0 / d = 0.0)
    (h: Int.less (OfNat 0) (Float.Theory.units x) = True):
    Int.leq (OfNat 0) (Float.Theory.units (x / d)) = True :=
  let lo: 0.0 <= x :=
    floatLeOfLt 0.0 x
      (Float.Theory.lessOfUnits 0.0 x
        (J (y w => Int.less y (Float.Theory.units x) = True) h (byComputing: OfNat 0 = Float.Theory.units 0.0)))
  Float.Theory.unitsNonneg (x / d) (J (y w => y <= x / d) (Float.divMonotone 0.0 x d pos fd lo) z0)

--| The same for a negative dividend.
theorem divNonposUnits ∀ (x d: Float)
    (pos: 0.0 < d)
    (fd: Float.isFinite d = True)
    (z0: -0.0 / d = -0.0)
    (h: Int.less (Float.Theory.units x) (OfNat 0) = True):
    Int.leq (Float.Theory.units (x / d)) (OfNat 0) = True :=
  let hi: x <= -0.0 :=
    floatLeOfLt x
      (-0.0)
      (Float.Theory.lessOfUnits x
        (-0.0)
        (J (y w => Int.less (Float.Theory.units x) y = True) h (byComputing: OfNat 0 = Float.Theory.units (-0.0))))
  J
    (y w => Int.leq (Float.Theory.units (x / d)) y = True)
    (Float.Theory.unitsMonoKey
      (x / d).bits
      (-0.0).bits
      (J (y w => x / d <= y) (Float.divMonotone x (-0.0) d pos fd hi) z0))
    (byComputing: Float.Theory.units (-0.0) = OfNat 0)

theorem shiftPositive ∀ (k t c d: Int) (b v tt w: Nat)
    (kAbs: Int.natAbs k = b * 36028797018963968)
    (vb: v ≤ b)
    (kPos: Int.less (OfNat 0) k = True)
    (tPos: Int.leq (OfNat 0) t = True)
    (et: Int.natAbs t = tt)
    (t2: b * 36028797018963968 ≤ tt * 10 + v * 14404 + 5)
    (dLo: Int.leq (Int.neg (OfNat (v * 6144))) d = True)
    (ew: w = v * 2048)
    (s1: Int.leq (Int.add t d) (Int.add c (OfNat w)) = True):
    Int.less (OfNat 0) c = True :=
  arithmetic [kAbs, vb, kPos, tPos, et, t2, dLo, ew, s1]

theorem shiftNegative ∀ (k t c d: Int) (b v tt w: Nat)
    (kAbs: Int.natAbs k = b * 36028797018963968)
    (vb: v ≤ b)
    (kNeg: Int.less k (OfNat 0) = True)
    (tNeg: Int.leq t (OfNat 0) = True)
    (et: Int.natAbs t = tt)
    (t2: b * 36028797018963968 ≤ tt * 10 + v * 14404 + 5)
    (dHi: Int.leq d (OfNat (v * 6144)) = True)
    (ew: w = v * 2048)
    (s2: Int.leq c (Int.add (Int.add t d) (OfNat w)) = True):
    Int.less c (OfNat 0) = True :=
  arithmetic [kAbs, vb, kNeg, tNeg, et, t2, dHi, ew, s2]

--| A double `tenthsSlack` below the tenth `k / 10.0` divides by 0.1 to below
--| `k`, for a whole double `k` of a nonzero `i` up to 3601 in size.
--|
--| The proof: by the standard model, `k / 10.0` is within `|k| · 2^-53` of
--| `k / 10`, the shifted value within 2^-44 of its exact value
--| (`slackSum`), and its quotient by 0.1 within 2^-53 of the exact one; the
--| errors, scaled back by ten, come to under 3.5 · 2^-41 at `|k| ≤ 3601`,
--| less than the 3 · 2^-44 · 10 the slack moves it.
theorem slackBelow ∀ (k: Float) (i: Int)
    (fk: Float.isFinite k = True)
    (whole: Float.Theory.units k = Int.mul i (OfNat (Float.Model.pow2 1074)))
    (nz: i ≠ OfNat 0)
    (h: Int.natAbs i ≤ 3601):
    (k / 10.0 - tenthsSlack) / 0.1 < k :=
  let v: Nat := Float.Model.pow2 1019
  let m: Nat := Int.natAbs i
  let b: Nat := m * v
  let bv: b ≤ v * 3601 := scaledBound m v h
  let vb: v ≤ b := atLeastOne m v (nonzeroSize i nz)
  let ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968 := wholeSize k i whole
  let t: Float := k / 10.0
  let ts := tenthSetup k b bv ku
  let tc := tenthCoarse k b bv ku fk ts.left
  let d: Float := -tenthsSlack
  let c: Float := t + d
  let sum := slackSum t d byComputing byComputing ts.right.left ts.right.right byComputing byComputing
  let cs := shiftSetup t d byComputing ts.right.left ts.right.right byComputing byComputing
  let qc := quotientCoarse c cs.right.left cs.right.right cs.left
  let tt: Nat := Int.natAbs (Float.Theory.units t)
  let lt: Int.less (Float.Theory.units (c / 0.1)) (Float.Theory.units k) = True :=
    Float.Theory.orCase
      [goal := Int.less (Float.Theory.units (c / 0.1)) (Float.Theory.units k) = True]
      (Float.Theory.boolCases (Int.leq (OfNat 0) (Float.Theory.units k)))
      (nonneg =>
        let kPos: Int.less (OfNat 0) (Float.Theory.units k) = True :=
          posOfNonzero
            (Float.Theory.units k)
            nonneg
            (J (y w => y ≠ OfNat 0) (Float.Theory.mulNonzero i (Float.Model.pow2 1074) byComputing nz) whole.flipped)
        let tPos := divNonnegUnits k 10.0 byComputing byComputing byComputing kPos
        let cPos :=
          shiftPositive
            (Float.Theory.units k)
            (Float.Theory.units t)
            (Float.Theory.units c)
            (Float.Theory.units d)
            b
            v
            tt
            (Float.Model.pow2 1030)
            ku
            vb
            kPos
            tPos
            byComputing
            tc.right
            byComputing
            byComputing
            sum.left
        let qPos := divNonnegUnits c 0.1 byComputing byComputing byComputing cPos
        slackBelowPos
          (Float.Theory.units k)
          (Float.Theory.units t)
          (Float.Theory.units c)
          (Float.Theory.units (c / 0.1))
          (Float.Theory.units d)
          b
          v
          tt
          (Int.natAbs (Float.Theory.units c))
          (Int.natAbs (Float.Theory.units (c / 0.1)))
          (Float.Model.pow2 1030)
          ku
          bv
          byComputing
          kPos
          tPos
          (Float.Theory.intLeOfLess (OfNat 0) (Float.Theory.units c) cPos)
          qPos
          byComputing
          byComputing
          byComputing
          tc.left
          byComputing
          byComputing
          sum.right
          qc.left)
      (notNonneg =>
        let kNeg: Int.less (Float.Theory.units k) (OfNat 0) = True :=
          Float.Theory.intLessZeroOfNotNonneg (Float.Theory.units k) notNonneg
        let tNeg := divNonposUnits k 10.0 byComputing byComputing byComputing kNeg
        let cNeg :=
          shiftNegative
            (Float.Theory.units k)
            (Float.Theory.units t)
            (Float.Theory.units c)
            (Float.Theory.units d)
            b
            v
            tt
            (Float.Model.pow2 1030)
            ku
            vb
            kNeg
            tNeg
            byComputing
            tc.right
            byComputing
            byComputing
            sum.right
        let qNeg := divNonposUnits c 0.1 byComputing byComputing byComputing cNeg
        slackBelowNeg
          (Float.Theory.units k)
          (Float.Theory.units t)
          (Float.Theory.units c)
          (Float.Theory.units (c / 0.1))
          (Float.Theory.units d)
          b
          v
          tt
          (Int.natAbs (Float.Theory.units c))
          (Int.natAbs (Float.Theory.units (c / 0.1)))
          (Float.Model.pow2 1030)
          ku
          bv
          byComputing
          kNeg
          tNeg
          (Float.Theory.intLeOfLess (Float.Theory.units c) (OfNat 0) cNeg)
          qNeg
          byComputing
          byComputing
          byComputing
          tc.right
          byComputing
          byComputing
          sum.right
          qc.right)
  J (y w => y / 0.1 < k) (Float.Theory.lessOfUnits (c / 0.1) k lt) (Float.subAddNeg t tenthsSlack).flipped

--| A double `tenthsSlack` above the tenth `k / 10.0` divides by 0.1 to above
--| `k`, as `slackBelow`.
theorem slackAbove ∀ (k: Float) (i: Int)
    (fk: Float.isFinite k = True)
    (whole: Float.Theory.units k = Int.mul i (OfNat (Float.Model.pow2 1074)))
    (nz: i ≠ OfNat 0)
    (h: Int.natAbs i ≤ 3601):
    k < (k / 10.0 + tenthsSlack) / 0.1 :=
  let v: Nat := Float.Model.pow2 1019
  let m: Nat := Int.natAbs i
  let b: Nat := m * v
  let bv: b ≤ v * 3601 := scaledBound m v h
  let vb: v ≤ b := atLeastOne m v (nonzeroSize i nz)
  let ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968 := wholeSize k i whole
  let t: Float := k / 10.0
  let ts := tenthSetup k b bv ku
  let tc := tenthCoarse k b bv ku fk ts.left
  let d: Float := tenthsSlack
  let c: Float := t + d
  let sum := slackSum t d byComputing byComputing ts.right.left ts.right.right byComputing byComputing
  let cs := shiftSetup t d byComputing ts.right.left ts.right.right byComputing byComputing
  let qc := quotientCoarse c cs.right.left cs.right.right cs.left
  let tt: Nat := Int.natAbs (Float.Theory.units t)
  let lt: Int.less (Float.Theory.units k) (Float.Theory.units (c / 0.1)) = True :=
    Float.Theory.orCase
      [goal := Int.less (Float.Theory.units k) (Float.Theory.units (c / 0.1)) = True]
      (Float.Theory.boolCases (Int.leq (OfNat 0) (Float.Theory.units k)))
      (nonneg =>
        let kPos: Int.less (OfNat 0) (Float.Theory.units k) = True :=
          posOfNonzero
            (Float.Theory.units k)
            nonneg
            (J (y w => y ≠ OfNat 0) (Float.Theory.mulNonzero i (Float.Model.pow2 1074) byComputing nz) whole.flipped)
        let tPos := divNonnegUnits k 10.0 byComputing byComputing byComputing kPos
        let cPos :=
          shiftPositive
            (Float.Theory.units k)
            (Float.Theory.units t)
            (Float.Theory.units c)
            (Float.Theory.units d)
            b
            v
            tt
            (Float.Model.pow2 1030)
            ku
            vb
            kPos
            tPos
            byComputing
            tc.right
            byComputing
            byComputing
            sum.left
        let qPos := divNonnegUnits c 0.1 byComputing byComputing byComputing cPos
        slackAbovePos
          (Float.Theory.units k)
          (Float.Theory.units t)
          (Float.Theory.units c)
          (Float.Theory.units (c / 0.1))
          (Float.Theory.units d)
          b
          v
          tt
          (Int.natAbs (Float.Theory.units c))
          (Int.natAbs (Float.Theory.units (c / 0.1)))
          (Float.Model.pow2 1030)
          ku
          bv
          byComputing
          kPos
          tPos
          (Float.Theory.intLeOfLess (OfNat 0) (Float.Theory.units c) cPos)
          qPos
          byComputing
          byComputing
          byComputing
          tc.right
          byComputing
          byComputing
          sum.left
          qc.right)
      (notNonneg =>
        let kNeg: Int.less (Float.Theory.units k) (OfNat 0) = True :=
          Float.Theory.intLessZeroOfNotNonneg (Float.Theory.units k) notNonneg
        let tNeg := divNonposUnits k 10.0 byComputing byComputing byComputing kNeg
        let cNeg :=
          shiftNegative
            (Float.Theory.units k)
            (Float.Theory.units t)
            (Float.Theory.units c)
            (Float.Theory.units d)
            b
            v
            tt
            (Float.Model.pow2 1030)
            ku
            vb
            kNeg
            tNeg
            byComputing
            tc.right
            byComputing
            byComputing
            sum.right
        let qNeg := divNonposUnits c 0.1 byComputing byComputing byComputing cNeg
        slackAboveNeg
          (Float.Theory.units k)
          (Float.Theory.units t)
          (Float.Theory.units c)
          (Float.Theory.units (c / 0.1))
          (Float.Theory.units d)
          b
          v
          tt
          (Int.natAbs (Float.Theory.units c))
          (Int.natAbs (Float.Theory.units (c / 0.1)))
          (Float.Model.pow2 1030)
          ku
          bv
          byComputing
          kNeg
          tNeg
          (Float.Theory.intLeOfLess (Float.Theory.units c) (OfNat 0) cNeg)
          qNeg
          byComputing
          byComputing
          byComputing
          tc.left
          byComputing
          byComputing
          sum.left
          qc.left)
  Float.Theory.lessOfUnits k (c / 0.1) lt

theorem zeroTenthsChecked ∀ (s: Bool): tenthsCheck (wholeAt (OfNat 0) s) = True := match s with
  | True => byComputing
  | False => byComputing

theorem tenthsSizeSmall ∀ (i: Int) (h: Int.natAbs i ≤ 3601): Int.natAbs i ≤ 9007199254740992 := arithmetic [h]

--| Every whole number of tenths up to 3601 in size, of either zero sign,
--| passes `tenthsCheck`: zero by computing, the rest by `tripNonzero`,
--| `slackBelow`, `slackAbove` and `tenthSetup`.
theorem tenthsAt ∀ (i: Int) (s: Bool) (h: Int.natAbs i ≤ 3601): tenthsCheck (wholeAt i s) = True :=
  Float.Theory.orCase
    [goal := tenthsCheck (wholeAt i s) = True]
    (Float.Theory.intZeroCases i)
    (i0 => J (y w => tenthsCheck (wholeAt y s) = True) (zeroTenthsChecked s) i0.flipped)
    (nz =>
      let k: Float := wholeAt i s
      let rs := Float.Theory.roundScaledWhole i s (tenthsSizeSmall i h)
      let kb: k.bits = Float.Model.roundScaled i 0 s :=
        Float.Theory.ofBitsBits (Float.Model.roundScaled i 0 s) (wholeAtValid i s)
      let fk: Float.isFinite k = True :=
        Float.Theory.isFiniteOf k (J (r w => Float.Theory.FiniteBits r) rs.left kb.flipped)
      let whole: Float.Theory.units k = Int.mul i (OfNat (Float.Model.pow2 1074)) :=
        J (r w => Float.Model.units r = Int.mul i (OfNat (Float.Model.pow2 1074))) rs.right kb.flipped
      let ts :=
        tenthSetup k
          (Int.natAbs i * Float.Model.pow2 1019)
          (scaledBound (Int.natAbs i) (Float.Model.pow2 1019) h)
          (wholeSize k i whole)
      let base: (Nat.equal k.bits k.bits
        ∧ (Float.less ((k / 10.0 - tenthsSlack) / 0.1) k
          ∧ (Float.less k ((k / 10.0 + tenthsSlack) / 0.1)
            ∧ (Float.leq (-361.0) (k / 10.0) ∧ Float.leq (k / 10.0) 361.0))))
        = True :=
        Bool.andIntro
          (Nat.equalRefl k.bits)
          (Bool.andIntro
            (slackBelow k i fk whole nz h)
            (Bool.andIntro (slackAbove k i fk whole nz h) (Bool.andIntro ts.right.left ts.right.right)))
      J
        (y w =>
          (Nat.equal y.bits k.bits
            ∧ (Float.less ((y / 10.0 - tenthsSlack) / 0.1) k
              ∧ (Float.less k ((y / 10.0 + tenthsSlack) / 0.1)
                ∧ (Float.leq (-361.0) (y / 10.0) ∧ Float.leq (y / 10.0) 361.0))))
            = True)
        base
        (tripNonzero k i fk whole nz h).flipped)

theorem tenfoldCoarse ∀ (z x v: Nat)
    (up: z * 9007199254740992 ≤ x * 9007199254740992 + x + 4503599627370496)
    (down: x * 9007199254740992 ≤ z * 9007199254740992 + x + 4503599627370496)
    (top: x ≤ v * 129775726862308212736):
    (z ≤ x + v * 14408 + 1) ∧ (x ≤ z + v * 14408 + 1) :=
  Both (arithmetic [up, top]) (arithmetic [down, top])

theorem labelNear ∀ (np u: Int) (b z tt v h p: Nat)
    (en: Int.natAbs np = b * 36028797018963968)
    (eu: Int.natAbs u = z)
    (eh: h = v * 18014398509481984)
    (ep: p = v * 36028797018963968)
    (v1: 1 ≤ v)
    (t1: tt * 10 ≤ b * 36028797018963968 + v * 14404 + 5)
    (t2: b * 36028797018963968 ≤ tt * 10 + v * 14404 + 5)
    (z1: z ≤ tt * 10 + v * 14408 + 1)
    (z2: tt * 10 ≤ z + v * 14408 + 1)
    (sign: ((Int.leq (OfNat 0) np = True) ∧ (Int.leq (OfNat 0) u = True))
      ∨ ((Int.less np (OfNat 0) = True) ∧ (Int.leq u (OfNat 0) = True))):
    (Int.leq np (Int.add u (OfNat h)) = True) ∧ (Int.less (Int.add u (OfNat h)) (Int.add np (OfNat p)) = True) :=
  match sign with
    | Inl s =>
      let s1 := s.left
      let s2 := s.right
      Both
        (arithmetic [en, eu, eh, ep, v1, t1, t2, z1, z2, s1, s2])
        (arithmetic [en, eu, eh, ep, v1, t1, t2, z1, z2, s1, s2])
    | Inr s =>
      let s1 := s.left
      let s2 := s.right
      Both
        (arithmetic [en, eu, eh, ep, v1, t1, t2, z1, z2, s1, s2])
        (arithmetic [en, eu, eh, ep, v1, t1, t2, z1, z2, s1, s2])

theorem tenfoldTop ∀ (tt b v: Nat)
    (bv: b ≤ v * 3601)
    (t1: tt * 10 ≤ b * 36028797018963968 + v * 14404 + 5)
    (v1: 1 ≤ v):
    tt * 10 ≤ v * 129775726862308212736 :=
  arithmetic [bv, t1, v1]

--| `round (k / 10.0 * 10.0) = k` for a whole double `k` of a nonzero `i` up
--| to 3601 in size: `/ 10.0` and `* 10.0` each miss by at most 2^-53 of the
--| value (the standard model), far under the half unit `round` allows.
theorem labelRound ∀ (k: Float) (i: Int)
    (fk: Float.isFinite k = True)
    (whole: Float.Theory.units k = Int.mul i (OfNat (Float.Model.pow2 1074)))
    (nz: i ≠ OfNat 0)
    (h: Int.natAbs i ≤ 3601):
    Float.round (k / 10.0 * 10.0) = k :=
  let v: Nat := Float.Model.pow2 1019
  let m: Nat := Int.natAbs i
  let b: Nat := m * v
  let bv: b ≤ v * 3601 := scaledBound m v h
  let ku: Int.natAbs (Float.Theory.units k) = b * 36028797018963968 := wholeSize k i whole
  let t: Float := k / 10.0
  let z: Float := t * 10.0
  let ts := tenthSetup k b bv ku
  let tc := tenthCoarse k b bv ku fk ts.left
  let tt: Nat := Int.natAbs (Float.Theory.units t)
  let zz: Nat := Int.natAbs (Float.Theory.units z)
  let tenUnits: Int.natAbs (Float.Theory.units 10.0) = Float.Model.pow2 1074 * 10 := byComputing
  let mb :=
    Float.mulBetween
      (-361.0)
      t
      361.0
      10.0
      byComputing
      byComputing
      ts.left
      byComputing
      byComputing
      byComputing
      byComputing
      ts.right.left
      ts.right.right
  let ttop: tt * 10 ≤ v * 129775726862308212736 := tenfoldTop tt b v bv tc.left byComputing
  let small: Int.natAbs (Int.mul (Float.Theory.units t) (Float.Theory.units 10.0))
    < Float.Model.pow2 1074 * Nat.pow 2 2097 :=
    J
      (x w => x < Float.Model.pow2 1074 * Nat.pow 2 2097)
      (Float.Theory.leLessTrans
        (tt * 10 * Float.Model.pow2 1074)
        (v * 129775726862308212736 * Float.Model.pow2 1074)
        (Float.Model.pow2 1074 * Nat.pow 2 2097)
        (Nat.leMulRight (tt * 10) (v * 129775726862308212736) (Float.Model.pow2 1074) ttop)
        byComputing)
      (calc Int.natAbs (Int.mul (Float.Theory.units t) (Float.Theory.units 10.0))
        _ = tt * Int.natAbs (Float.Theory.units 10.0) := Int.natAbsMul (Float.Theory.units t) (Float.Theory.units 10.0)
        _ = tt * (Float.Model.pow2 1074 * 10) := Eq.cong (x => tt * x) tenUnits
        _ = tt * 10 * Float.Model.pow2 1074 := algebra).flipped
  let err := Float.mulRelError t 10.0 ts.left byComputing mb.left small
  let two :=
    Float.Theory.relCancel zz
      (tt * 10)
      (Float.Model.pow2 1074)
      9007199254740992
      4503599627370496
      (zz * Float.Model.pow2 1074)
      (Int.natAbs (Int.mul (Float.Theory.units t) (Float.Theory.units 10.0)))
      (Float.Model.pow2 1074 * 4503599627370496)
      byComputing
      byComputing
      (calc Int.natAbs (Int.mul (Float.Theory.units t) (Float.Theory.units 10.0))
        _ = tt * Int.natAbs (Float.Theory.units 10.0) := Int.natAbsMul (Float.Theory.units t) (Float.Theory.units 10.0)
        _ = tt * (Float.Model.pow2 1074 * 10) := Eq.cong (x => tt * x) tenUnits
        _ = tt * 10 * Float.Model.pow2 1074 := algebra)
      byComputing
      err
  let zc := tenfoldCoarse zz (tt * 10) v two.left two.right ttop
  let sign: ((Int.leq (OfNat 0) (Float.Theory.units k) = True) ∧ (Int.leq (OfNat 0) (Float.Theory.units z) = True))
    ∨ ((Int.less (Float.Theory.units k) (OfNat 0) = True) ∧ (Int.leq (Float.Theory.units z) (OfNat 0) = True)) :=
    Float.Theory.orCase
      [goal := ((Int.leq (OfNat 0) (Float.Theory.units k) = True) ∧ (Int.leq (OfNat 0) (Float.Theory.units z) = True))
        ∨ ((Int.less (Float.Theory.units k) (OfNat 0) = True) ∧ (Int.leq (Float.Theory.units z) (OfNat 0) = True))]
      (Float.Theory.boolCases (Int.leq (OfNat 0) (Float.Theory.units k)))
      (nonneg =>
        let kPos: Int.less (OfNat 0) (Float.Theory.units k) = True :=
          posOfNonzero
            (Float.Theory.units k)
            nonneg
            (J (y w => y ≠ OfNat 0) (Float.Theory.mulNonzero i (Float.Model.pow2 1074) byComputing nz) whole.flipped)
        let k0: 0.0 <= k :=
          floatLeOfLt 0.0 k
            (Float.Theory.lessOfUnits 0.0 k
              (J
                (y w => Int.less y (Float.Theory.units k) = True)
                kPos
                (byComputing: OfNat 0 = Float.Theory.units 0.0)))
        let t0: 0.0 <= t :=
          J (y w => y <= t) (Float.divMonotone 0.0 k 10.0 byComputing byComputing k0) (byComputing: 0.0 / 10.0 = 0.0)
        let z0: 0.0 <= z :=
          J
            (y w => y <= z)
            (Float.mulMonotoneLeft 0.0 t 10.0 byComputing ts.left byComputing byComputing t0)
            (byComputing: 0.0 * 10.0 = 0.0)
        Inl (Both nonneg (Float.Theory.unitsNonneg z z0)))
      (notNonneg =>
        let kNeg: Int.less (Float.Theory.units k) (OfNat 0) = True :=
          Float.Theory.intLessZeroOfNotNonneg (Float.Theory.units k) notNonneg
        let k0: k <= -0.0 :=
          floatLeOfLt k
            (-0.0)
            (Float.Theory.lessOfUnits k
              (-0.0)
              (J
                (y w => Int.less (Float.Theory.units k) y = True)
                kNeg
                (byComputing: OfNat 0 = Float.Theory.units (-0.0))))
        let t0: t <= -0.0 :=
          J
            (y w => t <= y)
            (Float.divMonotone k (-0.0) 10.0 byComputing byComputing k0)
            (byComputing: -0.0 / 10.0 = -0.0)
        let z0: z <= -0.0 :=
          J
            (y w => z <= y)
            (Float.mulMonotoneLeft t (-0.0) 10.0 ts.left byComputing byComputing byComputing t0)
            (byComputing: -0.0 * 10.0 = -0.0)
        Inr
          (Both kNeg
            (J
              (y w => Int.leq (Float.Theory.units z) y = True)
              (Float.Theory.unitsMonoKey z.bits (-0.0).bits z0)
              (byComputing: Float.Theory.units (-0.0) = OfNat 0))))
  let near :=
    labelNear
      (Float.Theory.units k)
      (Float.Theory.units z)
      b
      zz
      tt
      v
      (Float.Model.pow2 1073)
      (Float.Model.pow2 1074)
      ku
      byComputing
      byComputing
      byComputing
      byComputing
      tc.left
      tc.right
      zc.left
      zc.right
      sign
  Float.roundNear z k i mb.left fk whole nz
    (J (y w => Int.leq y (Int.add (Float.Theory.units z) (OfNat (Float.Model.pow2 1073))) = True) near.left whole)
    (J
      (y w =>
        Int.less
          (Int.add (Float.Theory.units z) (OfNat (Float.Model.pow2 1073)))
          (Int.add y (OfNat (Float.Model.pow2 1074)))
          = True)
      near.right
      whole)

--| A whole double `wholeAt i s` up to 2^53 in size is finite with `i` whole units.
theorem wholeAtFacts ∀ (i: Int) (s: Bool)
    (h: Int.natAbs i ≤ 9007199254740992):
    (Float.isFinite (wholeAt i s) = True)
      ∧ (Float.Theory.units (wholeAt i s) = Int.mul i (OfNat (Float.Model.pow2 1074))) :=
  let rs := Float.Theory.roundScaledWhole i s h
  let kb: (wholeAt i s).bits = Float.Model.roundScaled i 0 s :=
    Float.Theory.ofBitsBits (Float.Model.roundScaled i 0 s) (wholeAtValid i s)
  Both
    (Float.Theory.isFiniteOf (wholeAt i s) (J (r w => Float.Theory.FiniteBits r) rs.left kb.flipped))
    (J (r w => Float.Model.units r = Int.mul i (OfNat (Float.Model.pow2 1074))) rs.right kb.flipped)

theorem roundTripOf ∀ (k: Float) (c: tenthsCheck k = True): Float.round (k * 0.1 * 10.0) = k :=
  Float.bitsExt
    (Float.round (k * 0.1 * 10.0))
    k
    (Nat.equalSound (Float.round (k * 0.1 * 10.0)).bits k.bits (Bool.andLeft c))

--| The round trip in `floorTo` and `ceilTo` at step 0.1: a whole double `k`
--| of `n` (up to 3601 in size) comes back from `round (k * 0.1 * 10.0)`,
--| though neither product need be exact: the standard model for `*`, twice,
--| keeps it within half a unit (`tripNonzero`); zeros of both signs by
--| computing.
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
      let kc: k <= c / 0.1 := Float.Theory.leTrans k (x / 0.1) (c / 0.1) (Float.floorLe (x / 0.1)) q
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
      let ck: c / 0.1 <= k := Float.Theory.leTrans (c / 0.1) (x / 0.1) k q (Float.ceilGe (x / 0.1))
      (floatLtIrrefl (c / 0.1) (floatLeLtTrans (c / 0.1) k (c / 0.1) ck lt)).impossible)
    (notAbove => arithmetic [notAbove, close])

--| A sum of `g` within 361° (`g` in units of 2^-1074, `w` = 2^1030) and
--| `n` of size 3w: the rounded sum `s` is within one `w` of `g + n`. The standard
--| model bounds `s`'s size; the sign cases give its direction.
theorem roundedSumWithin ∀ (g n s: Int) (w t: Nat)
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
        let below: Int.less sum (OfNat 0) = True := Float.Theory.intLessZeroOfNotNonneg sum neg
        let atMost: g + d <= 0.0 :=
          Float.Theory.addAtMost g d 0.0 fg fd byComputing
            (J (y z => Int.leq sum y = True) (Float.Theory.intLeOfLess sum (OfNat 0) below) zero.flipped)
            (b => byComputing)
        Inr (Both below (J (y z => Int.leq s y = True) (Float.Theory.unitsMonoKey (g + d).bits 0.0.bits atMost) zero)))
  roundedSumWithin (Float.Theory.units g) (Float.Theory.units d) s w (1 * Nat.pow 2 2097) w2 gLo gHi dSize err sign

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
--| in size, and for each such `k` the double `c` 3 · 2^-44 below
--| `tenthOf k` divides by 0.1 to below `k` (`tenthsCheck`, by `slackBelow`
--| from the standard model for `/`). If `x`
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

--| The sum of two doubles within 361° is finite and within 2^-43 of the exact
--| sum, in units of 2^-1074: `Float.Theory.sumNear` for [-361, 361], whose
--| units are 2^1030 · 6350779162034176 in size.
theorem sumNear361 ∀ (g d: Float)
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
  Float.Theory.sumNear g d
    (-361.0)
    361.0
    (Float.Model.pow2 1030)
    (Float.Model.pow2 1030 * 6350779162034176)
    byComputing
    byComputing
    byComputing
    byComputing
    lo
    hi
    dLo
    dHi
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

theorem marginArith ∀ (l d s f: Int) (w e: Nat)
    (ee: e = w * 10)
    (pw: 1 ≤ w)
    (dHi: Int.leq d (Int.neg (OfNat (w * 13))) = True)
    (near: Int.leq s (Int.add (Int.add l d) (OfNat (w * 2))) = True)
    (fs: Int.leq f s = True):
    Int.less (Int.add f (OfNat e)) l = True :=
  arithmetic [ee, pw, dHi, near, fs]

--| The exact margin at the lower edge: for a band at least 1e-11° wide, the
--| unrounded lower edge `lat - placeAt unit * width` is more than 10 · 2^-44
--| below the answer, in exact units, so neither `floorTo`'s error at step 0.1
--| (`floorToTenthBound`, 2^-42) nor that and `wrap`'s (`wrapNear`, 6 · 2^-44)
--| can carry it past the answer. (The margin is
--| 0.15 of the width; 1e-11° is far below any real band.)
--|
--| The proof: the edge is at most `lat - 0.15 * width` (`marginRow`), and
--| `0.15 * width` is at least `0.15 * 1e-11`, over 13 · 2^-44; the standard
--| model for the subtraction (`sumNear361`) loses at most 2^-43 of it.
theorem marginBelowExact ∀ (lat width unit: Float)
    (latLo: -361.0 <= lat)
    (latHi: lat <= 361.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 361.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    Int.less
      (Int.add (Float.Theory.units (lat - placeAt unit * width)) (OfNat (Float.Model.pow2 1030 * 10)))
      (Float.Theory.units lat)
      = True :=
  let fl: Float.isFinite lat = True := Float.finiteBetween (-361.0) lat 361.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 361.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
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
  let qHi: q <= 361.0 := Float.Theory.leTrans q width 361.0 sq.right.right wHi
  let nq: Float.isNaN q = False := Float.Theory.finiteNotNaN q.bits (Float.Theory.finiteBits q sq.left)
  let d: Float := -q
  let dHi: d <= -(0.15 * 1e-11) := Float.negAntitone (0.15 * 1e-11) q byComputing nq qLo
  let dLo: -361.0 <= d := Float.negAntitone q 361.0 nq byComputing qHi
  let e: lat - q = lat + d := Float.subAddNeg lat q
  let near :=
    (sumNear361 lat d latLo latHi dLo (Float.Theory.leTrans d (-(0.15 * 1e-11)) 361.0 dHi byComputing)).right.right
  let du: Int.leq (Float.Theory.units d) (Int.neg (OfNat (Float.Model.pow2 1030 * 13))) = True :=
    intLeTransOf
      (Float.Theory.units d)
      (Float.Theory.units (-(0.15 * 1e-11)))
      (Int.neg (OfNat (Float.Model.pow2 1030 * 13)))
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
    (Float.Model.pow2 1030 * 10)
    byComputing
    byComputing
    du
    near
    edge

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
    (ee: e = v * 8192)
    (g: r + v * 8192 ≤ wd):
    Int.leq (Int.add ur (OfNat e)) uw = True :=
  arithmetic [er, ew, ee, g]

theorem shareGap ∀ (r wd v: Nat)
    (pv: 1 ≤ v)
    (scaled: r * (9007199254740992 * 9007199254740992)
      ≤ wd * (7656119366529843 * 9007199254740992 + 7656119366529843) + 9007199254740992 * 4503599627370496)
    (big: v * 90071 ≤ wd):
    r + v * 8192 ≤ wd :=
  arithmetic [pv, scaled, big]

theorem posOfOne ∀ (v: Nat) (h: 1 ≤ v): 0 < v := arithmetic [h]

theorem shareAboveAt ∀ (width: Float) (v e: Nat)
    (pv: 1 ≤ v)
    (u85: Float.Theory.units 0.85 = OfNat (v * 7656119366529843))
    (u180: Float.Theory.units 180.0 = OfNat (v * 1621295865853378560))
    (u1e11: Int.leq (OfNat (v * 90071)) (Float.Theory.units 1e-11) = True)
    (p1074: Float.Model.pow2 1074 = v * 9007199254740992)
    (top: v * 1621295865853378560 * (v * 7656119366529843) < Float.Model.pow2 1074 * Nat.pow 2 2097)
    (ee: e = v * 8192)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0):
    Int.leq (Int.add (Float.Theory.units (0.85 * width)) (OfNat e)) (Float.Theory.units width) = True :=
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let r: Float := 0.85 * width
  let sr := shareOfWidth 0.85 width byComputing byComputing fw w0
  let wd: Nat := Int.natAbs (Float.Theory.units width)
  let rn: Nat := Int.natAbs (Float.Theory.units r)
  let wu: Float.Theory.units width = OfNat wd :=
    intOfNonneg (Float.Theory.units width) (Float.Theory.unitsNonneg width w0)
  let ru: Float.Theory.units r = OfNat rn :=
    intOfNonneg (Float.Theory.units r) (Float.Theory.unitsNonneg r sr.right.left)
  let prod: Int.mul (Float.Theory.units 0.85) (Float.Theory.units width) = OfNat (v * 7656119366529843 * wd) :=
    Eq.trans (Eq.cong2 Int.mul u85 wu) (Float.Theory.intMulOfNat (v * 7656119366529843) wd)
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
      (Float.Theory.relCancelScaled rn wd v 7656119366529843 9007199254740992 4503599627370496 (posOfOne v pv) err2)
      big
  shareFinal (Float.Theory.units r) (Float.Theory.units width) rn wd v e ru wu ee gap

--| `0.85 * width` is at least 16 · 2^-44 below `width`, in exact units, for
--| a width from 1e-11° to 180°: the standard model for `*` puts it within
--| 2^-53 of 0.85 of the width, and 0.15 of 1e-11° is over 26 · 2^-44.
theorem shareAbove ∀ (width: Float)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0):
    Int.leq
      (Int.add (Float.Theory.units (0.85 * width)) (OfNat (Float.Model.pow2 1030 * 16)))
      (Float.Theory.units width)
      = True :=
  shareAboveAt width
    (Float.Model.pow2 1021)
    (Float.Model.pow2 1030 * 16)
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
    (ee: e = w * 10)
    (pw: 1 ≤ w)
    (dn: dd = Int.neg rr)
    (core: Int.leq (Int.add rr (OfNat (w * 16))) wd = True)
    (s1: Int.leq (Int.add l dd) (Int.add c (OfNat (w * 2))) = True)
    (s2: Int.leq (Int.add c wd) (Int.add t2 (OfNat (w * 2))) = True)
    (mono: Int.leq t2 t = True):
    Int.less (Int.add l (OfNat e)) t = True :=
  arithmetic [ee, pw, dn, core, s1, s2, mono]

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
      (Float.negAntitone (a * width) 180.0 n byComputing (Float.Theory.leTrans (a * width) width 180.0 high wHi))
      (Float.negAntitone 0.0 (a * width) byComputing n low))

--| The exact margin at the upper edge: for a band from 1e-11° to 180° wide
--| around `lat` within 180°, the unrounded upper edge `from + width` is more
--| than 10 · 2^-44 above the answer, in exact units, so `ceilTo`'s error at
--| step 0.1 (`ceilToTenthBound`) can't carry it below the answer.
--|
--| The proof: `from` is at least `lat - 0.85 * width` (`marginRow`), so
--| `from + width` is at least `(lat - 0.85 * width) + width`, which the
--| standard model for `+` (`sumNear361`, twice) puts within 2^-42 of
--| `lat + (width - 0.85 * width)`, and `shareAbove` puts the bracket over
--| 16 · 2^-44.
theorem marginAboveExact ∀ (lat width unit: Float)
    (latLo: -180.0 <= lat)
    (latHi: lat <= 180.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    Int.less
      (Int.add (Float.Theory.units lat) (OfNat (Float.Model.pow2 1030 * 10)))
      (Float.Theory.units (lat - placeAt unit * width + width))
      = True :=
  let fl: Float.isFinite lat = True := Float.finiteBetween (-180.0) lat 180.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let lLo: -361.0 <= lat := Float.Theory.leTrans (-361.0) (-180.0) lat byComputing latLo
  let lHi: lat <= 361.0 := Float.Theory.leTrans lat 180.0 361.0 latHi byComputing
  let row := marginRow lat width unit fl fw w0 low high
  let fr: Float := lat - placeAt unit * width
  let r: Float := 0.85 * width
  let sr := shareOfWidth 0.85 width byComputing byComputing fw w0
  let nr := negShare 0.85 width sr.left sr.right.left sr.right.right wHi
  let d: Float := -r
  let fd: Float.isFinite d = True :=
    Float.finiteBetween (-180.0) d (-0.0) byComputing byComputing nr.right.left nr.right.right
  let dLo: -361.0 <= d := Float.Theory.leTrans (-361.0) (-180.0) d byComputing nr.right.left
  let dHi: d <= 361.0 := Float.Theory.leTrans d (-0.0) 361.0 nr.right.right byComputing
  let s1 := sumNear361 lat d lLo lHi dLo dHi
  let c: Float := lat + d
  let cLo: -361.0 <= c :=
    Float.Theory.leTrans
      (-361.0)
      (-180.0 + -180.0)
      c
      byComputing
      (Float.Theory.leTrans
        (-180.0 + -180.0)
        (-180.0 + d)
        c
        (Float.addMonotone (-180.0) d (-180.0) byComputing fd byComputing nr.right.left)
        (Float.addMonotoneLeft (-180.0) lat d byComputing fl fd latLo))
  let cHi: c <= 361.0 :=
    Float.Theory.leTrans c
      (180.0 + -0.0)
      361.0
      (Float.Theory.leTrans c
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
    sumNear361 lat
      (-q)
      lLo
      lHi
      (Float.Theory.leTrans (-361.0) (-180.0) (-q) byComputing nq.right.left)
      (Float.Theory.leTrans (-q) (-0.0) 361.0 nq.right.right byComputing)
  let fUpper: Float.isFinite (lat - q) = True :=
    J (y z => Float.isFinite y = True) s0.left (Float.subAddNeg lat q).flipped
  let ffr: Float.isFinite fr = True := Float.finiteBetween c fr (lat - q) s1.left fUpper cfr row.right
  let t1: c + width <= fr + width := Float.addMonotoneLeft c fr width s1.left ffr fw cfr
  let s2 :=
    sumNear361 c width cLo cHi
      (Float.Theory.leTrans (-361.0) 0.0 width byComputing w0)
      (Float.Theory.leTrans width 180.0 361.0 wHi byComputing)
  marginUpArith
    (Float.Theory.units lat)
    (Float.Theory.units d)
    (Float.Theory.units r)
    (Float.Theory.units c)
    (Float.Theory.units width)
    (Float.Theory.units (c + width))
    (Float.Theory.units (fr + width))
    (Float.Model.pow2 1030)
    (Float.Model.pow2 1030 * 10)
    byComputing
    byComputing
    (Float.Theory.unitsNeg r nr.left)
    (shareAbove width wLo wHi)
    s1.right.left
    s2.right.left
    (Float.Theory.unitsMonoKey (c + width).bits (fr + width).bits t1)

-- Longitude: `wrap` on whole degrees

--| Where `wrap` sends the whole number `n` of degrees: `n` shifted by a
--| multiple of 360 into [-180, 180).
def wrappedDegrees (n: Int): Int := Int.sub (OfNat (Int.modNat (Int.add n (OfNat 180)) 360)) (OfNat 180)

theorem stepArith ∀ (s: Bool) (f: Int) (a q r: Nat)
    (ea: Int.natAbs f = a)
    (ef: f = Int.signed s a)
    (low: q * 360 ≤ a)
    (high: a < q * 360 + 360)
    (er: r = a - q * 360):
    (f = Int.add (Int.mul (Int.signed s q) (OfNat 360)) (Int.signed s r))
      ∧ ((Int.natAbs (Int.signed s r) < 360)
        ∧ (Int.leq (OfNat 0) f = True → Int.leq (OfNat 0) (Int.signed s r) = True)) :=
  match s with
    | False =>
      Both (arithmetic [ea, ef, low, high, er]) (Both (arithmetic [ea, ef, low, high, er]) (n => arithmetic [n]))
    | True =>
      Both
        (arithmetic [ea, ef, low, high, er])
        (Both (arithmetic [ea, ef, low, high, er]) (n => arithmetic [n, ea, ef, low, high, er]))

theorem zeroOfMulZero ∀ (a p: Nat) (pp: 0 < p) (e: a * p = 0): a = 0 := match a with
  | Zero => byComputing
  | Succ k => (arithmetic [e, Float.Theory.mulPos (Succ k) p byComputing pp]: Void).impossible

--| A whole number of units has the sign its double's sign bit says.
theorem signOfScaled ∀ (f: Int) (s: Bool) (p: Nat)
    (pp: 0 < p)
    (e: Int.mul f (OfNat p) = Int.signed s (Int.natAbs f * p)):
    f = Int.signed s (Int.natAbs f) :=
  match s, f with
    | False, OfNat a => byComputing
    | False, NegSucc a =>
      let pos: 0 < Succ a * p := Float.Theory.mulPos (Succ a) p byComputing pp
      let e2: Int.neg (OfNat (Succ a * p)) = OfNat (Succ a * p) := Eq.trans (Float.Theory.negSuccMul a p).flipped e
      (arithmetic [e2, pos]: Void).impossible
    | True, OfNat a =>
      let e2: OfNat (a * p) = Int.neg (OfNat (a * p)) :=
        Eq.trans (algebra: OfNat (a * p) = Int.mul (OfNat a) (OfNat p)) e
      let z: a * p = 0 := arithmetic [e2]
      let a0: a = 0 := zeroOfMulZero a p pp z
      rewrite a0
    | True, NegSucc a => byComputing

theorem subScaledOf ∀ (a b c p: Nat) (e: a = b + c): a * p - b * p = c * p :=
  let e2: (b + c) * p = b * p + c * p := algebra
  rewrite e then arithmetic [e2]

theorem subScaled ∀ (a b p: Nat) (h: b ≤ a): a * p - b * p = (a - b) * p := subScaledOf a b (a - b) p (arithmetic [h])

--| The whole-number side of `remWholeStep`, for `m = a·p` units over
--| `d = 360·p`: the quotient `q` has `360q ≤ a < 360q + 360`, and the
--| remainder is `(a - 360q)·p`.
theorem remCore ∀ (m d a p: Nat)
    (pp: 0 < p)
    (em: m = a * p)
    (ed: d = p * 360):
    (Nat.divFuel m m d * 360 ≤ a)
      ∧ ((a < Nat.divFuel m m d * 360 + 360) ∧ (m - Nat.divFuel m m d * d = (a - Nat.divFuel m m d * 360) * p)) :=
  let q: Nat := Nat.divFuel m m d
  let dpos: 0 < d := rewrite ed then arithmetic [pp]
  let low0: q * d ≤ m := Nat.divFuelLe m m d
  let high0: m < Succ q * d := Nat.divFuelBound m m d (Nat.nonzeroOfPos d dpos) (Nat.leRefl m)
  let low: q * 360 ≤ a :=
    Float.Theory.cancelLe
      (q * 360)
      a
      p
      pp
      (rewrite (algebra: q * 360 * p = q * (p * 360)), ed.flipped, em.flipped then low0)
  let high: a < q * 360 + 360 :=
    Float.Theory.cancelLess a
      (q * 360 + 360)
      p
      (rewrite em.flipped, (algebra: (q * 360 + 360) * p = Succ q * (p * 360)), ed.flipped then high0)
  Both low
    (Both high
      (calc m - q * d
        _ = a * p - q * (p * 360) := Eq.cong2 (x y => x - q * y) em ed
        _ = a * p - q * 360 * p := Eq.cong (y => a * p - y) (algebra: q * (p * 360) = q * 360 * p)
        _ = (a - q * 360) * p := subScaled a (q * 360) p low))

--| `x % 360.0` for `x` of a whole number `f` of degrees: exactly `g`
--| degrees, where `f = 360 t + g`, `|g| < 360` and `g` has `f`'s sign.
theorem remWholeStep ∀ (x: Float) (f: Int)
    (fx: Float.isFinite x = True)
    (ux: Float.Theory.units x = Int.mul f (OfNat (Float.Model.pow2 1074)))
    [goal: Prop]
    (k: ∀ (g t: Int) => Float.Theory.units (x % 360.0) = Int.mul g (OfNat (Float.Model.pow2 1074))
      → f = Int.add (Int.mul t (OfNat 360)) g
      → Int.natAbs g < 360
      → (Int.leq (OfNat 0) f = True → Int.leq (OfNat 0) g = True)
      → goal):
    goal :=
  let s: Bool := Float.Model.signBit x.bits
  let a: Nat := Int.natAbs f
  let m: Nat := Int.natAbs (Float.Theory.units x)
  let d: Nat := Int.natAbs (Float.Theory.units 360.0)
  let em: m = a * Float.Model.pow2 1074 :=
    Eq.trans (Eq.cong Int.natAbs ux) (Int.natAbsMul f (OfNat (Float.Model.pow2 1074)))
  let q: Nat := Nat.divFuel m m d
  let core := remCore m d a (Float.Model.pow2 1074) byComputing em byComputing
  let r: Nat := a - q * 360
  let uxs: Float.Theory.units x = Int.signed s (a * Float.Model.pow2 1074) :=
    J (y w => Float.Theory.units x = Int.signed s y) (Float.Theory.unitsSigned x.bits).flipped em
  let ef: f = Int.signed s a := signOfScaled f s (Float.Model.pow2 1074) byComputing (Eq.trans ux.flipped uxs)
  let sa := stepArith s f a q r byComputing ef core.left core.right.left byComputing
  k
    (Int.signed s r)
    (Int.signed s q)
    (calc Float.Theory.units (x % 360.0)
      _ = Int.signed s (m - q * d) := Float.Theory.remUnitsExact x 360.0 fx byComputing byComputing
      _ = Int.signed s (r * Float.Model.pow2 1074) := Eq.cong (y => Int.signed s y) core.right.right
      _ = Int.mul (Int.signed s r) (OfNat (Float.Model.pow2 1074)) :=
        Float.Theory.signedScaled s r (Float.Model.pow2 1074))
    sa.left
    sa.right.left
    sa.right.right

theorem wrapShiftSize ∀ (n: Int) (h: Int.natAbs n ≤ 400): Int.natAbs (Int.add n (OfNat 180)) ≤ 9007199254740992 :=
  arithmetic [h]

theorem wrapLiftSize ∀ (g: Int) (h: Int.natAbs g < 360): Int.natAbs (Int.add g (OfNat 360)) ≤ 9007199254740992 :=
  arithmetic [h]

theorem wrapBackSize ∀ (g: Int)
    (h: Int.natAbs g < 360):
    Int.natAbs (Int.add g (Int.neg (OfNat 180))) ≤ 9007199254740992 :=
  arithmetic [h]

theorem modOf ∀ (f t: Int) (r: Nat)
    (e: f = Int.add (Int.mul t (OfNat 360)) (OfNat r))
    (h: r < 360):
    Int.modNat f 360 = r :=
  let m := Int.modNatToInt f 360
  arithmetic [e, h, m]

--| The integers' side of `wrap` on whole degrees: two truncating remainders
--| by 360 with 360 added between are the floored one.
theorem wrapArith ∀ (n g1 t1 g2 t2: Int)
    (e1: Int.add n (OfNat 180) = Int.add (Int.mul t1 (OfNat 360)) g1)
    (s1: Int.natAbs g1 < 360)
    (e2: Int.add g1 (OfNat 360) = Int.add (Int.mul t2 (OfNat 360)) g2)
    (s2: Int.natAbs g2 < 360)
    (p2: Int.leq (OfNat 0) g2 = True):
    Int.add g2 (Int.neg (OfNat 180)) = wrappedDegrees n :=
  let r: Nat := Int.natAbs g2
  let er: g2 = OfNat r := arithmetic [p2]
  let m: Int.modNat (Int.add n (OfNat 180)) 360 = r :=
    modOf (Int.add n (OfNat 180)) (Int.sub (Int.add t1 t2) (OfNat 1)) r (arithmetic [e1, e2, er]) (arithmetic [s2, er])
  rewrite m then arithmetic [er]

theorem liftNonneg ∀ (g: Int) (h: Int.natAbs g < 360): Int.leq (OfNat 0) (Int.add g (OfNat 360)) = True :=
  arithmetic [h]

--| `wrap` of a whole number `n` of degrees, up to 400 in size, is exactly
--| `wrappedDegrees n`: `n` shifted by a multiple of 360 into [-180, 180).
--| (Tenths are another matter: `wrapTenth`.) Every step is exact on whole
--| numbers: the sums by `addWholeExact`, the remainders by `remWholeStep`
--| (`x % 360.0` is `x` less a whole number of 360s, with `x`'s sign), and
--| `wrapArith` is the integers' side.
theorem wrapWholeExact ∀ (e: Float) (n: Int)
    (fe: Float.isFinite e = True)
    (whole: Float.Theory.units e = Int.mul n (OfNat (Float.Model.pow2 1074)))
    (h: Int.natAbs n ≤ 400):
    Float.Theory.units (wrap e) = Int.mul (wrappedDegrees n) (OfNat (Float.Model.pow2 1074)) :=
  let a1: Float := e + 180.0
  let s1 := Float.Theory.addWholeExact e 180.0 n (OfNat 180) fe byComputing whole byComputing (wrapShiftSize n h)
  remWholeStep a1
    (Int.add n (OfNat 180))
    s1.left
    s1.right
    [goal := Float.Theory.units (wrap e) = Int.mul (wrappedDegrees n) (OfNat (Float.Model.pow2 1074))]
    (g1 t1 u1 e1 z1 p1 =>
      let r1: Float := a1 % 360.0
      let f1: Float.isFinite r1 = True := (Float.Theory.remUnits a1 360.0 s1.left byComputing byComputing).left
      let s2 := Float.Theory.addWholeExact r1 360.0 g1 (OfNat 360) f1 byComputing u1 byComputing (wrapLiftSize g1 z1)
      let a2: Float := r1 + 360.0
      remWholeStep a2
        (Int.add g1 (OfNat 360))
        s2.left
        s2.right
        [goal := Float.Theory.units (wrap e) = Int.mul (wrappedDegrees n) (OfNat (Float.Model.pow2 1074))]
        (g2 t2 u2 e2 z2 p2 =>
          let r2: Float := a2 % 360.0
          let f2: Float.isFinite r2 = True := (Float.Theory.remUnits a2 360.0 s2.left byComputing byComputing).left
          let s3 :=
            Float.Theory.addWholeExact r2
              (-180.0)
              g2
              (Int.neg (OfNat 180))
              f2
              byComputing
              u2
              byComputing
              (wrapBackSize g2 z2)
          let back: Int.add g2 (Int.neg (OfNat 180)) = wrappedDegrees n :=
            wrapArith n g1 t1 g2 t2 e1 z1 e2 z2 (p2 (liftNonneg g1 z1))
          J
            (y w => Float.Theory.units y = Int.mul (wrappedDegrees n) (OfNat (Float.Model.pow2 1074)))
            (J (i w => Float.Theory.units (r2 + (-180.0)) = Int.mul i (OfNat (Float.Model.pow2 1074))) s3.right back)
            (Float.subAddNeg r2 180.0).flipped))

-- The answer in its band: latitude

theorem unitsWithinDegrees ∀ (u lo hi: Int) (p: Nat)
    (pp: 0 < p)
    (el: lo = Int.neg (OfNat (p * 360)))
    (eh: hi = OfNat (p * 360))
    (a: Int.leq lo u = True)
    (b: Int.leq u hi = True):
    Int.natAbs u < p * 361 :=
  arithmetic [pp, el, eh, a, b]

--| A double from -360° to 360° has under 361 · 2^1074 units in size.
theorem unitsWithin360 ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    Int.natAbs (Float.Theory.units x) < Float.Model.pow2 1074 * 361 :=
  unitsWithinDegrees
    (Float.Theory.units x)
    (Float.Theory.units (-360.0))
    (Float.Theory.units 360.0)
    (Float.Model.pow2 1074)
    byComputing
    byComputing
    byComputing
    (Float.Theory.unitsMonoKey (-360.0).bits x.bits lo)
    (Float.Theory.unitsMonoKey x.bits 360.0.bits hi)

--| A band rounds its edges to tenths or to whole degrees.
theorem stepEither ∀ (width: Float): (stepFor width = 0.1) ∨ (stepFor width = 1.0) :=
  match n: Float.ieeeLt width 5.0 with
    | True => Inl byComputing
    | False => Inr byComputing

theorem leAddNat ∀ (a b: Int) (p: Nat) (h: Int.leq a b = True): Int.leq a (Int.add b (OfNat p)) = True := arithmetic [h]

--| `floorTo x 0.1` for `|x| ≤ 360` is a tenth within 361°, so finite.
theorem floorTenthFinite ∀ (x: Float) (lo: -360.0 <= x) (hi: x <= 360.0): Float.isFinite (floorTo x 0.1) = True :=
  let bounds := Bool.andRight (Bool.andRight (Bool.andRight (floorTenthsChecked x lo hi)))
  (Float.finiteBetween
    (-361.0)
    (tenthOf (Float.floor (x / 0.1)))
    361.0
    byComputing
    byComputing
    (Bool.andLeft bounds)
    (Bool.andRight bounds): Float.isFinite (tenthOf (Float.floor (x / 0.1))) = True)

--| `ceilTo x 0.1` for `|x| ≤ 360` is a tenth within 361°, so finite.
theorem ceilTenthFinite ∀ (x: Float) (lo: -360.0 <= x) (hi: x <= 360.0): Float.isFinite (ceilTo x 0.1) = True :=
  let bounds := Bool.andRight (Bool.andRight (Bool.andRight (ceilTenthsChecked x lo hi)))
  (Float.finiteBetween
    (-361.0)
    (tenthOf (Float.ceil (x / 0.1)))
    361.0
    byComputing
    byComputing
    (Bool.andLeft bounds)
    (Bool.andRight bounds): Float.isFinite (tenthOf (Float.ceil (x / 0.1))) = True)

--| Outward rounding at a band's step moves a lower edge `x` within 360° up
--| by at most 2^-42, in exact units, and leaves it finite: at step 0.1 by
--| `floorToTenthBound`, at step 1 not at all (`floorTo x 1.0` is `floor x`).
theorem floorStepBound ∀ (x width: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    (Float.isFinite (floorTo x (stepFor width)) = True)
      ∧ (Int.leq
        (Float.Theory.units (floorTo x (stepFor width)))
        (Int.add (Float.Theory.units x) (OfNat (Float.Model.pow2 1032)))
        = True) :=
  match stepEither width with
    | Inl e =>
      J
        (s z =>
          (Float.isFinite (floorTo x s) = True)
            ∧ (Int.leq
              (Float.Theory.units (floorTo x s))
              (Int.add (Float.Theory.units x) (OfNat (Float.Model.pow2 1032)))
              = True))
        (Both (floorTenthFinite x lo hi) (floorToTenthBound x lo hi))
        e.flipped
    | Inr e =>
      let w: floorTo x 1.0 = Float.floor x :=
        floorToWhole x (Float.Theory.absBelowOf x 360.0 562949953421312.0 byComputing lo hi byComputing)
      let b: Int.leq
        (Float.Theory.units (Float.floor x))
        (Int.add (Float.Theory.units x) (OfNat (Float.Model.pow2 1032)))
        = True :=
        leAddNat
          (Float.Theory.units (Float.floor x))
          (Float.Theory.units x)
          (Float.Model.pow2 1032)
          (Float.Theory.unitsMonoKey (Float.floor x).bits x.bits (Float.floorLe x))
      J
        (s z =>
          (Float.isFinite (floorTo x s) = True)
            ∧ (Int.leq
              (Float.Theory.units (floorTo x s))
              (Int.add (Float.Theory.units x) (OfNat (Float.Model.pow2 1032)))
              = True))
        (J
          (y z =>
            (Float.isFinite y = True)
              ∧ (Int.leq (Float.Theory.units y) (Int.add (Float.Theory.units x) (OfNat (Float.Model.pow2 1032)))
                = True))
          (Both
            (Float.floorIsFinite x (Float.Theory.absBelowOf x 360.0 9007199254740992.0 byComputing lo hi byComputing))
            b)
          w.flipped)
        e.flipped

--| Outward rounding at a band's step moves an upper edge `x` within 360°
--| down by at most 2^-42, in exact units, and leaves it finite, as
--| `floorStepBound`.
theorem ceilStepBound ∀ (x width: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    (Float.isFinite (ceilTo x (stepFor width)) = True)
      ∧ (Int.leq
        (Float.Theory.units x)
        (Int.add (Float.Theory.units (ceilTo x (stepFor width))) (OfNat (Float.Model.pow2 1032)))
        = True) :=
  match stepEither width with
    | Inl e =>
      J
        (s z =>
          (Float.isFinite (ceilTo x s) = True)
            ∧ (Int.leq
              (Float.Theory.units x)
              (Int.add (Float.Theory.units (ceilTo x s)) (OfNat (Float.Model.pow2 1032)))
              = True))
        (Both (ceilTenthFinite x lo hi) (ceilToTenthBound x lo hi))
        e.flipped
    | Inr e =>
      let w: ceilTo x 1.0 = Float.ceil x :=
        ceilToWhole x (Float.Theory.absBelowOf x 360.0 562949953421312.0 byComputing lo hi byComputing)
      let b: Int.leq
        (Float.Theory.units x)
        (Int.add (Float.Theory.units (Float.ceil x)) (OfNat (Float.Model.pow2 1032)))
        = True :=
        leAddNat
          (Float.Theory.units x)
          (Float.Theory.units (Float.ceil x))
          (Float.Model.pow2 1032)
          (Float.Theory.unitsMonoKey x.bits (Float.ceil x).bits (Float.ceilGe x))
      J
        (s z =>
          (Float.isFinite (ceilTo x s) = True)
            ∧ (Int.leq
              (Float.Theory.units x)
              (Int.add (Float.Theory.units (ceilTo x s)) (OfNat (Float.Model.pow2 1032)))
              = True))
        (J
          (y z =>
            (Float.isFinite y = True)
              ∧ (Int.leq (Float.Theory.units x) (Int.add (Float.Theory.units y) (OfNat (Float.Model.pow2 1032)))
                = True))
          (Both
            (Float.ceilIsFinite x (Float.Theory.absBelowOf x 360.0 9007199254740992.0 byComputing lo hi byComputing))
            b)
          w.flipped)
        e.flipped

-- Outward rounding moves an edge by at most a step

--| `x / 0.1` for `|x| ≤ 360` is from -3600 to 3600.
theorem quotientWithin3600 ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    (-3600.0 <= x / 0.1) ∧ (x / 0.1 <= 3600.0) :=
  Both
    (J
      (z w => z <= x / 0.1)
      (Float.divMonotone (-360.0) x 0.1 byComputing byComputing lo)
      (byComputing: -360.0 / 0.1 = -3600.0))
    (J
      (z w => x / 0.1 <= z)
      (Float.divMonotone x 360.0 0.1 byComputing byComputing hi)
      (byComputing: 360.0 / 0.1 = 3600.0))

theorem zeroOfNeither ∀ (u: Int) (a: Int.less (OfNat 0) u = False) (b: Int.less u (OfNat 0) = False): u = OfNat 0 :=
  arithmetic [a, b]

theorem quotientNearArith ∀ (q c: Int) (w: Nat)
    (cb: Int.natAbs c ≤ w * 13042424520864956416)
    (up: Int.natAbs q * 3602879701896397 ≤ Int.natAbs c * 36028797018963972 + 3602879701896397)
    (down: Int.natAbs c * 36028797018963964 ≤ Int.natAbs q * 3602879701896397 + 3602879701896397)
    (sign: ((Int.less (OfNat 0) c = True) ∧ (Int.leq (OfNat 0) q = True))
      ∨ (((Int.less c (OfNat 0) = True) ∧ (Int.leq q (OfNat 0) = True)) ∨ (c = OfNat 0))):
    (Int.leq
      (Int.mul q (OfNat 3602879701896397))
      (Int.add (Int.mul c (OfNat 36028797018963968)) (OfNat (w * 52169698083459825664 + 3602879701896397)))
      = True)
      ∧ (Int.leq
        (Int.mul c (OfNat 36028797018963968))
        (Int.add (Int.mul q (OfNat 3602879701896397)) (OfNat (w * 52169698083459825664 + 3602879701896397)))
        = True) :=
  match sign with
    | Inl b =>
      let b1 := b.left
      let b2 := b.right
      Both (arithmetic [cb, up, down, b1, b2]) (arithmetic [cb, up, down, b1, b2])
    | Inr r =>
      match r with
        | Inl b =>
          let b1 := b.left
          let b2 := b.right
          Both (arithmetic [cb, up, down, b1, b2]) (arithmetic [cb, up, down, b1, b2])
        | Inr z => Both (arithmetic [cb, up, down, z]) (arithmetic [cb, up, down, z])

--| `c / 0.1` for `c` within 362°, signed: the quotient's units times 0.1's
--| significand are within `4 · 362° + 0.1's significand` of `c`'s units
--| times 2^55, either way (in units of 2^-1074; `w` is 2^1019).
--| `quotientCoarse` bounds the sizes, and the quotient has `c`'s sign
--| (`divNonnegUnits`, `divNonposUnits`); at `c = 0` the quotient is at most
--| one unit in size.
theorem quotientNear ∀ (c: Float)
    (lo: -362.0 <= c)
    (hi: c <= 362.0)
    (fq: Float.isFinite (c / 0.1) = True):
    (Int.leq
      (Int.mul (Float.Theory.units (c / 0.1)) (OfNat 3602879701896397))
      (Int.add
        (Int.mul (Float.Theory.units c) (OfNat 36028797018963968))
        (OfNat (Float.Model.pow2 1019 * 52169698083459825664 + 3602879701896397)))
      = True)
      ∧ (Int.leq
        (Int.mul (Float.Theory.units c) (OfNat 36028797018963968))
        (Int.add
          (Int.mul (Float.Theory.units (c / 0.1)) (OfNat 3602879701896397))
          (OfNat (Float.Model.pow2 1019 * 52169698083459825664 + 3602879701896397)))
        = True) :=
  let uc: Int := Float.Theory.units c
  let uq: Int := Float.Theory.units (c / 0.1)
  let qc := quotientCoarse c lo hi fq
  let cb: Int.natAbs uc ≤ Float.Model.pow2 1019 * 13042424520864956416 :=
    natAbsWithin uc
      (Float.Theory.units (-362.0))
      (Float.Theory.units 362.0)
      (Float.Model.pow2 1019 * 13042424520864956416)
      byComputing
      byComputing
      (Float.Theory.unitsMonoKey (-362.0).bits c.bits lo)
      (Float.Theory.unitsMonoKey c.bits 362.0.bits hi)
  let sign: ((Int.less (OfNat 0) uc = True) ∧ (Int.leq (OfNat 0) uq = True))
    ∨ (((Int.less uc (OfNat 0) = True) ∧ (Int.leq uq (OfNat 0) = True)) ∨ (uc = OfNat 0)) :=
    Float.Theory.orCase
      [goal := ((Int.less (OfNat 0) uc = True) ∧ (Int.leq (OfNat 0) uq = True))
        ∨ (((Int.less uc (OfNat 0) = True) ∧ (Int.leq uq (OfNat 0) = True)) ∨ (uc = OfNat 0))]
      (Float.Theory.boolCases (Int.less (OfNat 0) uc))
      (pos => Inl (Both pos (divNonnegUnits c 0.1 byComputing byComputing byComputing pos)))
      (npos =>
        Float.Theory.orCase
          [goal := ((Int.less (OfNat 0) uc = True) ∧ (Int.leq (OfNat 0) uq = True))
            ∨ (((Int.less uc (OfNat 0) = True) ∧ (Int.leq uq (OfNat 0) = True)) ∨ (uc = OfNat 0))]
          (Float.Theory.boolCases (Int.less uc (OfNat 0)))
          (neg => Inr (Inl (Both neg (divNonposUnits c 0.1 byComputing byComputing byComputing neg))))
          (nneg => Inr (Inr (zeroOfNeither uc npos nneg))))
  quotientNearArith uq uc (Float.Model.pow2 1019) cb qc.left qc.right sign

theorem floorTenthArith ∀ (ux uq uk uqc uc ut ud u2: Int) (bigU v w: Nat)
    (a: Int.leq
      (Int.mul ux (OfNat 36028797018963968))
      (Int.add (Int.mul uq (OfNat 3602879701896397)) (OfNat (w * 52169698083459825664 + 3602879701896397)))
      = True)
    (b: Int.less uq (Int.add uk (OfNat bigU)) = True)
    (c: Int.leq uk uqc = True)
    (d: Int.leq
      (Int.mul uqc (OfNat 3602879701896397))
      (Int.add (Int.mul uc (OfNat 36028797018963968)) (OfNat (w * 52169698083459825664 + 3602879701896397)))
      = True)
    (e: Int.leq uc (Int.add (Int.add ut ud) (OfNat v)) = True)
    (eD: ud = OfNat (3 * v))
    (ev: v = w * 2048)
    (eU: bigU = w * 36028797018963968)
    (e2: u2 = OfNat (bigU * 2)):
    Int.leq ux (Int.add ut u2) = True :=
  arithmetic [a, b, c, d, e, eD, ev, eU, e2]

theorem ceilTenthArith ∀ (ux uq uk uqc uc ut ud u2: Int) (bigU v w: Nat)
    (a: Int.leq
      (Int.mul uq (OfNat 3602879701896397))
      (Int.add (Int.mul ux (OfNat 36028797018963968)) (OfNat (w * 52169698083459825664 + 3602879701896397)))
      = True)
    (b: Int.less uk (Int.add uq (OfNat bigU)) = True)
    (c: Int.leq uqc uk = True)
    (d: Int.leq
      (Int.mul uc (OfNat 36028797018963968))
      (Int.add (Int.mul uqc (OfNat 3602879701896397)) (OfNat (w * 52169698083459825664 + 3602879701896397)))
      = True)
    (e: Int.leq (Int.add ut ud) (Int.add uc (OfNat v)) = True)
    (eD: ud = Int.neg (OfNat (3 * v)))
    (ev: v = w * 2048)
    (eU: bigU = w * 36028797018963968)
    (e2: u2 = OfNat (bigU * 2)):
    Int.leq ut (Int.add ux u2) = True :=
  arithmetic [a, b, c, d, e, eD, ev, eU, e2]

--| Rounding down to tenths moves `x` within 360° by at most 2° (in fact
--| about 0.1°), in exact units: `x ≤ floorTo x 0.1 + 2`. With `k` =
--| `floor (x / 0.1)` and `t` its tenth, `x / 0.1 < k + 1` exactly
--| (`floorUnitsAbove`), `k` is below `(t + tenthsSlack) / 0.1`
--| (`tenthsCheck`), and the signed standard model for `/ 0.1`
--| (`quotientNear`) and `+` (`slackSum`) turn that back into degrees.
theorem floorTenthCoarse ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    Int.leq (Float.Theory.units x) (Int.add (Float.Theory.units (floorTo x 0.1)) (Float.Theory.units 2.0)) = True :=
  let y: Float := x / 0.1
  let k: Float := Float.floor y
  let g: Float := tenthOf k
  let rest := Bool.andRight (floorTenthsChecked x lo hi)
  let lt: k < (g + tenthsSlack) / 0.1 := Bool.andLeft (Bool.andRight rest)
  let bounds := Bool.andRight (Bool.andRight rest)
  let ss := shiftSetup g tenthsSlack byComputing (Bool.andLeft bounds) (Bool.andRight bounds) byComputing byComputing
  let sum :=
    slackSum g tenthsSlack byComputing byComputing (Bool.andLeft bounds) (Bool.andRight bounds) byComputing byComputing
  let yr := quotientWithin3600 x lo hi
  let qx :=
    quotientNear x
      (Float.Theory.leTrans (-362.0) (-360.0) x byComputing lo)
      (Float.Theory.leTrans x 360.0 362.0 hi byComputing)
      (tenthsQuotient x lo hi).left
  let qc := quotientNear (g + tenthsSlack) ss.right.left ss.right.right ss.left
  floorTenthArith
    (Float.Theory.units x)
    (Float.Theory.units y)
    (Float.Theory.units k)
    (Float.Theory.units ((g + tenthsSlack) / 0.1))
    (Float.Theory.units (g + tenthsSlack))
    (Float.Theory.units g)
    (Float.Theory.units tenthsSlack)
    (Float.Theory.units 2.0)
    (Float.Model.pow2 1074)
    (Float.Model.pow2 1030)
    (Float.Model.pow2 1019)
    qx.right
    (Float.Theory.floorUnitsAbove y
      (Float.Theory.absBelowOf y 3600.0 9007199254740992.0 byComputing yr.left yr.right byComputing))
    (Float.Theory.unitsMonoKey k.bits ((g + tenthsSlack) / 0.1).bits (floatLeOfLt k ((g + tenthsSlack) / 0.1) lt))
    qc.left
    sum.right
    byComputing
    byComputing
    byComputing
    byComputing

--| Rounding up to tenths moves `x` within 360° by at most 2°, in exact
--| units: `ceilTo x 0.1 ≤ x + 2`, as `floorTenthCoarse`.
theorem ceilTenthCoarse ∀ (x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    Int.leq (Float.Theory.units (ceilTo x 0.1)) (Int.add (Float.Theory.units x) (Float.Theory.units 2.0)) = True :=
  let y: Float := x / 0.1
  let k: Float := Float.ceil y
  let g: Float := tenthOf k
  let d: Float := -tenthsSlack
  let rest := Bool.andRight (ceilTenthsChecked x lo hi)
  let lt: (g + d) / 0.1 < k := J (z w => z / 0.1 < k) (Bool.andLeft rest) (Float.subAddNeg g tenthsSlack)
  let bounds := Bool.andRight (Bool.andRight rest)
  let ss := shiftSetup g d byComputing (Bool.andLeft bounds) (Bool.andRight bounds) byComputing byComputing
  let sum := slackSum g d byComputing byComputing (Bool.andLeft bounds) (Bool.andRight bounds) byComputing byComputing
  let yr := quotientWithin3600 x lo hi
  let qx :=
    quotientNear x
      (Float.Theory.leTrans (-362.0) (-360.0) x byComputing lo)
      (Float.Theory.leTrans x 360.0 362.0 hi byComputing)
      (tenthsQuotient x lo hi).left
  let qc := quotientNear (g + d) ss.right.left ss.right.right ss.left
  ceilTenthArith
    (Float.Theory.units x)
    (Float.Theory.units y)
    (Float.Theory.units k)
    (Float.Theory.units ((g + d) / 0.1))
    (Float.Theory.units (g + d))
    (Float.Theory.units g)
    (Float.Theory.units d)
    (Float.Theory.units 2.0)
    (Float.Model.pow2 1074)
    (Float.Model.pow2 1030)
    (Float.Model.pow2 1019)
    qx.left
    (Float.Theory.ceilUnitsBelow y
      (Float.Theory.absBelowOf y 3600.0 9007199254740992.0 byComputing yr.left yr.right byComputing))
    (Float.Theory.unitsMonoKey ((g + d) / 0.1).bits k.bits (floatLeOfLt ((g + d) / 0.1) k lt))
    qc.right
    sum.left
    byComputing
    byComputing
    byComputing
    byComputing

theorem wholeStepArith ∀ (ux uf u2: Int) (bigU: Nat)
    (h: Int.less ux (Int.add uf (OfNat bigU)) = True)
    (e2: u2 = OfNat (bigU * 2)):
    Int.leq ux (Int.add uf u2) = True :=
  arithmetic [h, e2]

--| Outward rounding at a band's step moves a lower edge `x` within 360°
--| down by at most 2° (by at most a step, 1° or about 0.1°, in fact), in
--| exact units: at step 0.1 by `floorTenthCoarse`, at step 1 because
--| `floorTo x 1.0` is `floor x`, less than 1 below `x` (`floorUnitsAbove`).
theorem floorCoarse ∀ (width x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    Int.leq (Float.Theory.units x) (Int.add (Float.Theory.units (floorTo x (stepFor width))) (Float.Theory.units 2.0))
      = True :=
  match stepEither width with
    | Inl e =>
      J
        (s z =>
          Int.leq (Float.Theory.units x) (Int.add (Float.Theory.units (floorTo x s)) (Float.Theory.units 2.0)) = True)
        (floorTenthCoarse x lo hi)
        e.flipped
    | Inr e =>
      let small: Float.abs x < 9007199254740992.0 :=
        Float.Theory.absBelowOf x 360.0 9007199254740992.0 byComputing lo hi byComputing
      J
        (s z =>
          Int.leq (Float.Theory.units x) (Int.add (Float.Theory.units (floorTo x s)) (Float.Theory.units 2.0)) = True)
        (J
          (y z => Int.leq (Float.Theory.units x) (Int.add (Float.Theory.units y) (Float.Theory.units 2.0)) = True)
          (wholeStepArith
            (Float.Theory.units x)
            (Float.Theory.units (Float.floor x))
            (Float.Theory.units 2.0)
            (Float.Model.pow2 1074)
            (Float.Theory.floorUnitsAbove x small)
            byComputing)
          (floorToWhole x (Float.Theory.absBelowOf x 360.0 562949953421312.0 byComputing lo hi byComputing)).flipped)
        e.flipped

--| Outward rounding at a band's step moves an upper edge `x` within 360°
--| up by at most 2°, in exact units, as `floorCoarse` (`ceilUnitsBelow`).
theorem ceilCoarse ∀ (width x: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0):
    Int.leq (Float.Theory.units (ceilTo x (stepFor width))) (Int.add (Float.Theory.units x) (Float.Theory.units 2.0))
      = True :=
  match stepEither width with
    | Inl e =>
      J
        (s z =>
          Int.leq (Float.Theory.units (ceilTo x s)) (Int.add (Float.Theory.units x) (Float.Theory.units 2.0)) = True)
        (ceilTenthCoarse x lo hi)
        e.flipped
    | Inr e =>
      let small: Float.abs x < 9007199254740992.0 :=
        Float.Theory.absBelowOf x 360.0 9007199254740992.0 byComputing lo hi byComputing
      J
        (s z =>
          Int.leq (Float.Theory.units (ceilTo x s)) (Int.add (Float.Theory.units x) (Float.Theory.units 2.0)) = True)
        (J
          (y z => Int.leq (Float.Theory.units y) (Int.add (Float.Theory.units x) (Float.Theory.units 2.0)) = True)
          (wholeStepArith
            (Float.Theory.units (Float.ceil x))
            (Float.Theory.units x)
            (Float.Theory.units 2.0)
            (Float.Model.pow2 1074)
            (Float.Theory.ceilUnitsBelow x small)
            byComputing)
          (ceilToWhole x (Float.Theory.absBelowOf x 360.0 562949953421312.0 byComputing lo hi byComputing)).flipped)
        e.flipped

theorem lessOfAddNat ∀ (a b: Int) (p: Nat) (h: Int.less (Int.add a (OfNat p)) b = True): Int.less a b = True :=
  arithmetic [h]

theorem notNaNOfFinite ∀ (x: Float) (f: Float.isFinite x = True): Float.isNaN x = False :=
  Float.Theory.finiteNotNaN x.bits (Float.Theory.finiteBits x f)

--| The unclamped lower edge of a latitude band, `lat - placeAt unit * width`,
--| is finite, at least -270° and below the answer.
theorem unclampedFacts ∀ (lat width unit: Float)
    (latLo: -90.0 <= lat)
    (latHi: lat <= 90.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    (Float.isFinite (lat - placeAt unit * width) = True)
      ∧ ((-270.0 <= lat - placeAt unit * width) ∧ (lat - placeAt unit * width < lat)) :=
  let unc: Float := lat - placeAt unit * width
  let fl: Float.isFinite lat = True := Float.finiteBetween (-90.0) lat 90.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let row := marginRow lat width unit fl fw w0 low high
  let s85 := shareOfWidth 0.85 width byComputing byComputing fw w0
  let a: -90.0 - 0.85 * width <= lat - 0.85 * width :=
    Float.subMonotoneLeft (-90.0) lat (0.85 * width) byComputing fl s85.left latLo
  let b: -90.0 - 180.0 <= -90.0 - 0.85 * width :=
    Float.subAntitoneRight
      (-90.0)
      (0.85 * width)
      180.0
      byComputing
      s85.left
      byComputing
      (Float.Theory.leTrans (0.85 * width) width 180.0 s85.right.right wHi)
  let lo: -270.0 <= unc :=
    J
      (y z => y <= unc)
      (Float.Theory.leTrans
        (-90.0 - 180.0)
        (lat - 0.85 * width)
        unc
        (Float.Theory.leTrans (-90.0 - 180.0) (-90.0 - 0.85 * width) (lat - 0.85 * width) b a)
        row.left)
      (byComputing: -90.0 - 180.0 = -270.0)
  let lt: unc < lat :=
    Float.Theory.lessOfUnits unc lat
      (lessOfAddNat
        (Float.Theory.units unc)
        (Float.Theory.units lat)
        (Float.Model.pow2 1030 * 10)
        (marginBelowExact lat width unit
          (Float.Theory.leTrans (-361.0) (-90.0) lat byComputing latLo)
          (Float.Theory.leTrans lat 90.0 361.0 latHi byComputing)
          wLo
          (Float.Theory.leTrans width 180.0 361.0 wHi byComputing)
          low
          high))
  Both (Float.finiteBetween (-270.0) unc lat byComputing fl lo (floatLeOfLt unc lat lt)) (Both lo lt)

--| `90 - width` for a width from 0 to 180° is finite and from -90° to 90°.
theorem topEdgeRange ∀ (width: Float)
    (fw: Float.isFinite width = True)
    (w0: 0.0 <= width)
    (wHi: width <= 180.0):
    (Float.isFinite (90.0 - width) = True) ∧ ((-90.0 <= 90.0 - width) ∧ (90.0 - width <= 90.0)) :=
  let lo: -90.0 <= 90.0 - width :=
    J
      (y z => y <= 90.0 - width)
      (Float.subAntitoneRight 90.0 width 180.0 byComputing fw byComputing wHi)
      (byComputing: 90.0 - 180.0 = -90.0)
  let hi: 90.0 - width <= 90.0 :=
    J
      (y z => 90.0 - width <= y)
      (Float.subAntitoneRight 90.0 0.0 width byComputing byComputing fw w0)
      (byComputing: 90.0 - 0.0 = 90.0)
  Both (Float.finiteBetween (-90.0) (90.0 - width) 90.0 byComputing byComputing lo hi) (Both lo hi)

theorem chainBelow ∀ (a b c d: Int) (p q: Nat)
    (pq: p ≤ q)
    (h1: Int.leq a (Int.add b (OfNat p)) = True)
    (h2: Int.leq b c = True)
    (h3: Int.less (Int.add c (OfNat q)) d = True):
    Int.less a d = True :=
  arithmetic [pq, h1, h2, h3]

--| `floorTo (-90.0)` is -90° at either step.
theorem floorAtSouthPole ∀ (width: Float): floorTo (-90.0) (stepFor width) = -90.0 := match stepEither width with
  | Inl e => J (s z => floorTo (-90.0) s = -90.0) byComputing e.flipped
  | Inr e => J (s z => floorTo (-90.0) s = -90.0) byComputing e.flipped

--| A latitude band's lower edge is at most the answer, by JS's `<=`, for
--| the answer within [-90°, 90°], a width from 1e-11° to 180° (`latitudeWidthRange`
--| gives one from the tolerance) and `unit` from 0 to 1.
--|
--| The proof: when the edge isn't clamped at -90°, it is at most the
--| unclamped edge, which is more than 2^-42 below the answer
--| (`marginBelowExact`), and rounding moves it up by at most 2^-42
--| (`floorStepBound`). When it is clamped, it is -90° exactly (`90 - width`
--| is at least -90°), which both steps keep.
theorem latitudeFromBelow ∀ (lat width unit: Float)
    (latLo: -90.0 <= lat)
    (latHi: lat <= 90.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    Float.ieeeLe (latitudeBand lat width (placeAt unit)).from.value lat = True :=
  let fl: Float.isFinite lat = True := Float.finiteBetween (-90.0) lat 90.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let unc: Float := lat - placeAt unit * width
  let u := unclampedFacts lat width unit latLo latHi wLo wHi low high
  let nu: Float.isNaN unc = False := notNaNOfFinite unc u.left
  let m: Float := Float.max unc (-90.0)
  let nm: Float.isNaN m = False := Float.maxNotNaN unc (-90.0) nu byComputing
  let top := topEdgeRange width fw w0 wHi
  let nt: Float.isNaN (90.0 - width) = False := notNaNOfFinite (90.0 - width) top.left
  let from: Float := Float.min m (90.0 - width)
  let fromM: from <= m := Float.minLeLeft m (90.0 - width) nm nt
  let fromLo: -90.0 <= from :=
    Float.leMin m (90.0 - width) (-90.0) nm nt (Float.leMaxRight unc (-90.0) nu byComputing) top.right.left
  let fromHi: from <= 90.0 :=
    Float.Theory.leTrans from (90.0 - width) 90.0 (Float.minLeRight m (90.0 - width) nm nt) top.right.right
  let step: Float := stepFor width
  let fs :=
    floorStepBound from width
      (Float.Theory.leTrans (-360.0) (-90.0) from byComputing fromLo)
      (Float.Theory.leTrans from 90.0 360.0 fromHi byComputing)
  let nf: Float.isNaN (floorTo from step) = False := notNaNOfFinite (floorTo from step) fs.left
  let below: floorTo from step <= lat :=
    Float.Theory.orCase
      (Float.maxEither unc (-90.0) nu byComputing)
      (e =>
        let fu: from <= unc := J (y z => from <= y) fromM e
        floatLeOfLt
          (floorTo from step)
          lat
          (Float.Theory.lessOfUnits
            (floorTo from step)
            lat
            (chainBelow
              (Float.Theory.units (floorTo from step))
              (Float.Theory.units from)
              (Float.Theory.units unc)
              (Float.Theory.units lat)
              (Float.Model.pow2 1032)
              (Float.Model.pow2 1030 * 10)
              byComputing
              fs.right
              (Float.Theory.unitsMonoKey from.bits unc.bits fu)
              (marginBelowExact lat width unit
                (Float.Theory.leTrans (-361.0) (-90.0) lat byComputing latLo)
                (Float.Theory.leTrans lat 90.0 361.0 latHi byComputing)
                wLo
                (Float.Theory.leTrans width 180.0 361.0 wHi byComputing)
                low
                high))))
      (e =>
        let atPole: from = -90.0 := Ord.leAntisymm from (-90.0) (J (y z => from <= y) fromM e) fromLo
        J (y z => floorTo y step <= lat) (J (y z => y <= lat) latLo (floorAtSouthPole width).flipped) atPole.flipped)
  Float.ieeeLeOfLe
    (Float.max (-90.0) (floorTo from step))
    lat
    (Float.maxNotNaN (-90.0) (floorTo from step) byComputing nf)
    (notNaNOfFinite lat fl)
    (clampFromKeeps lat (floorTo from step) nf latLo below)

theorem chainAbove ∀ (l a b c: Int) (p q: Nat)
    (pq: p ≤ q)
    (h1: Int.less (Int.add l (OfNat q)) a = True)
    (h2: Int.leq a b = True)
    (h3: Int.leq b (Int.add c (OfNat p)) = True):
    Int.less l c = True :=
  arithmetic [pq, h1, h2, h3]

--| An edge from -90° to 90° plus a width from 0 to 180° is from -90° to 270°.
theorem edgePlusWidth ∀ (from width: Float)
    (fromLo: -90.0 <= from)
    (fromHi: from <= 90.0)
    (fw: Float.isFinite width = True)
    (w0: 0.0 <= width)
    (wHi: width <= 180.0):
    (-360.0 <= from + width) ∧ (from + width <= 360.0) :=
  let ff: Float.isFinite from = True := Float.finiteBetween (-90.0) from 90.0 byComputing byComputing fromLo fromHi
  let lo: -90.0 + 0.0 <= from + width :=
    Float.Theory.leTrans
      (-90.0 + 0.0)
      (from + 0.0)
      (from + width)
      (Float.addMonotoneLeft (-90.0) from 0.0 byComputing ff byComputing fromLo)
      (Float.addMonotone 0.0 width from byComputing fw ff w0)
  let hi: from + width <= 90.0 + 180.0 :=
    Float.Theory.leTrans
      (from + width)
      (90.0 + width)
      (90.0 + 180.0)
      (Float.addMonotoneLeft from 90.0 width ff byComputing fw fromHi)
      (Float.addMonotone width 180.0 90.0 fw byComputing byComputing wHi)
  Both
    (Float.Theory.leTrans (-360.0) (-90.0 + 0.0) (from + width) byComputing lo)
    (Float.Theory.leTrans (from + width) (90.0 + 180.0) 360.0 hi byComputing)

--| The upper edge `to` of a latitude band is at least the answer, by JS's
--| `<=`, when the band isn't clamped at 90°: its unrounded `from` is the
--| lower edge clamped at -90° only, so at least the unclamped one, and
--| `from + width` is more than 2^-42 above the answer
--| (`marginAboveExact`), which rounding moves down by at most 2^-42
--| (`ceilStepBound`).
theorem latitudeToAboveUnclamped ∀ (lat width unit: Float)
    (latLo: -90.0 <= lat)
    (latHi: lat <= 90.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0)
    (notTop: Float.min (Float.max (lat - placeAt unit * width) (-90.0)) (90.0 - width)
      = Float.max (lat - placeAt unit * width) (-90.0)):
    Float.ieeeLe lat (latitudeBand lat width (placeAt unit)).to.value = True :=
  let fl: Float.isFinite lat = True := Float.finiteBetween (-90.0) lat 90.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let unc: Float := lat - placeAt unit * width
  let u := unclampedFacts lat width unit latLo latHi wLo wHi low high
  let nu: Float.isNaN unc = False := notNaNOfFinite unc u.left
  let m: Float := Float.max unc (-90.0)
  let nm: Float.isNaN m = False := Float.maxNotNaN unc (-90.0) nu byComputing
  let top := topEdgeRange width fw w0 wHi
  let nt: Float.isNaN (90.0 - width) = False := notNaNOfFinite (90.0 - width) top.left
  let from: Float := Float.min m (90.0 - width)
  let fromLo: -90.0 <= from :=
    Float.leMin m (90.0 - width) (-90.0) nm nt (Float.leMaxRight unc (-90.0) nu byComputing) top.right.left
  let fromHi: from <= 90.0 :=
    Float.Theory.leTrans from (90.0 - width) 90.0 (Float.minLeRight m (90.0 - width) nm nt) top.right.right
  let ff: Float.isFinite from = True := Float.finiteBetween (-90.0) from 90.0 byComputing byComputing fromLo fromHi
  let uf: unc <= from := J (y z => unc <= y) (Float.leMaxLeft unc (-90.0) nu byComputing) notTop.flipped
  let step: Float := stepFor width
  let r := edgePlusWidth from width fromLo fromHi fw w0 wHi
  let cs := ceilStepBound (from + width) width r.left r.right
  let c: Float := ceilTo (from + width) step
  let nc: Float.isNaN c = False := notNaNOfFinite c cs.left
  let lt: lat < c :=
    Float.Theory.lessOfUnits lat c
      (chainAbove
        (Float.Theory.units lat)
        (Float.Theory.units (unc + width))
        (Float.Theory.units (from + width))
        (Float.Theory.units c)
        (Float.Model.pow2 1032)
        (Float.Model.pow2 1030 * 10)
        byComputing
        (marginAboveExact lat width unit
          (Float.Theory.leTrans (-180.0) (-90.0) lat byComputing latLo)
          (Float.Theory.leTrans lat 90.0 180.0 latHi byComputing)
          wLo
          wHi
          low
          high)
        (Float.Theory.unitsMonoKey
          (unc + width).bits
          (from + width).bits
          (Float.addMonotoneLeft unc from width u.left ff fw uf))
        cs.right)
  Float.ieeeLeOfLe lat
    (Float.min 90.0 c)
    (notNaNOfFinite lat fl)
    (Float.minNotNaN 90.0 c byComputing nc)
    (clampToKeeps lat c nc latHi (floatLeOfLt lat c lt))

theorem posOfLeMul ∀ (u: Int) (k p: Nat)
    (pk: 1 ≤ k)
    (pp: 0 < p)
    (h: Int.leq (OfNat (k * p)) u = True):
    Int.less (OfNat 0) u = True :=
  arithmetic [h, pp, Nat.leMulRight 1 k p pk]

theorem nearNinetyArith ∀ (n90 nw dneg q x u: Int) (w: Nat)
    (dn: dneg = Int.neg nw)
    (s1: Int.leq (Int.add n90 dneg) (Int.add q (OfNat (w * 2))) = True)
    (s2: Int.leq (Int.add q nw) (Int.add x (OfNat (w * 2))) = True)
    (gap: Int.less (Int.add u (OfNat (w * 4))) n90 = True):
    Int.less u x = True :=
  arithmetic [dn, s1, s2, gap]

--| `(90 - width) + width`, the upper edge of a band clamped at 90°, is
--| above 89.95°: each rounding moves it by at most 2^-43 (`sumNear361`). (It is
--| 90 exactly in a search of millions of widths, but the standard model
--| alone doesn't show that.)
theorem nearNinety ∀ (width: Float) (wLo: 1e-11 <= width) (wHi: width <= 180.0): 89.95 < 90.0 - width + width :=
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let nw: Float.isNaN width = False := notNaNOfFinite width fw
  let top := topEdgeRange width fw w0 wHi
  let q: Float := 90.0 - width
  let dLo: -361.0 <= -width :=
    Float.negAntitone width 361.0 nw byComputing (Float.Theory.leTrans width 180.0 361.0 wHi byComputing)
  let dHi: -width <= 361.0 :=
    Float.Theory.leTrans (-width) (-1e-11) 361.0 (Float.negAntitone 1e-11 width byComputing nw wLo) byComputing
  let s1 := sumNear361 90.0 (-width) byComputing byComputing dLo dHi
  let s1q: Int.leq
    (Int.add (Float.Theory.units 90.0) (Float.Theory.units (-width)))
    (Int.add (Float.Theory.units q) (OfNat (Float.Model.pow2 1030 * 2)))
    = True :=
    J
      (y z =>
        Int.leq
          (Int.add (Float.Theory.units 90.0) (Float.Theory.units (-width)))
          (Int.add (Float.Theory.units y) (OfNat (Float.Model.pow2 1030 * 2)))
          = True)
      s1.right.left
      (Float.subAddNeg 90.0 width).flipped
  let s2 :=
    sumNear361 q width
      (Float.Theory.leTrans (-361.0) (-90.0) q byComputing top.right.left)
      (Float.Theory.leTrans q 90.0 361.0 top.right.right byComputing)
      (Float.Theory.leTrans (-361.0) 0.0 width byComputing w0)
      (Float.Theory.leTrans width 180.0 361.0 wHi byComputing)
  Float.Theory.lessOfUnits 89.95
    (q + width)
    (nearNinetyArith
      (Float.Theory.units 90.0)
      (Float.Theory.units width)
      (Float.Theory.units (-width))
      (Float.Theory.units q)
      (Float.Theory.units (q + width))
      (Float.Theory.units 89.95)
      (Float.Model.pow2 1030)
      (Float.Theory.unitsNeg width nw)
      s1q
      s2.right.left
      byComputing)

--| An upper edge above 89.95° rounds up to at least 90° at either step:
--| `ceil` is whole, so above 899.5 tenths (or 89.5 degrees) it reaches 900
--| (or 90) (`Float.Theory.ceilAtLeast`).
theorem ceilStepAtLeastNinety ∀ (x width: Float)
    (lo: -360.0 <= x)
    (hi: x <= 360.0)
    (near: 89.95 < x):
    90.0 <= ceilTo x (stepFor width) :=
  let near2: 89.95 <= x := floatLeOfLt 89.95 x near
  Float.Theory.orCase
    (stepEither width)
    (e =>
      let y: Float := x / 0.1
      let pos: 0.0 < 0.1 := byComputing
      let f01: Float.isFinite 0.1 = True := byComputing
      let yNear: 899.5 <= y :=
        J (z w => z <= y) (Float.divMonotone 89.95 x 0.1 pos f01 near2) (byComputing: 89.95 / 0.1 = 899.5)
      let yLo: -3600.0 <= y :=
        J (z w => z <= y) (Float.divMonotone (-360.0) x 0.1 pos f01 lo) (byComputing: -360.0 / 0.1 = -3600.0)
      let yHi: y <= 3600.0 :=
        J (z w => y <= z) (Float.divMonotone x 360.0 0.1 pos f01 hi) (byComputing: 360.0 / 0.1 = 3600.0)
      let hu: Int.leq (OfNat ((2 * 899 + 1) * Float.Model.pow2 1073)) (Float.Theory.units y) = True :=
        J
          (v z => Int.leq v (Float.Theory.units y) = True)
          (Float.Theory.unitsMonoKey 899.5.bits y.bits yNear)
          (byComputing: Float.Theory.units 899.5 = OfNat ((2 * 899 + 1) * Float.Model.pow2 1073))
      let cu :=
        Float.Theory.ceilAtLeast y 899
          (Float.Theory.absBelowOf y 3600.0 9007199254740992.0 byComputing yLo yHi byComputing)
          hu
      let c900: 900.0 <= Float.ceil y :=
        Float.Theory.leOfUnitsPos 900.0
          (Float.ceil y)
          (posOfLeMul (Float.Theory.units (Float.ceil y)) (899 + 1) (Float.Model.pow2 1074) byComputing byComputing cu)
          (J
            (v z => Int.leq v (Float.Theory.units (Float.ceil y)) = True)
            cu
            (byComputing: OfNat ((899 + 1) * Float.Model.pow2 1074) = Float.Theory.units 900.0))
      let d: 900.0 / 10.0 <= Float.ceil y / 10.0 :=
        Float.divMonotone 900.0 (Float.ceil y) 10.0 byComputing byComputing c900
      let r: 90.0 <= Float.ceil y / 10.0 := J (v z => v <= Float.ceil y / 10.0) d (byComputing: 900.0 / 10.0 = 90.0)
      let r2: 90.0 <= ceilTo x 0.1 := J (v z => 90.0 <= v) r (ceilToTenth x lo hi).flipped
      J (st z => 90.0 <= ceilTo x st) r2 e.flipped)
    (e =>
      let xLo: -3600.0 <= x := Float.Theory.leTrans (-3600.0) (-360.0) x byComputing lo
      let xHi: x <= 3600.0 := Float.Theory.leTrans x 360.0 3600.0 hi byComputing
      let hu: Int.leq (OfNat ((2 * 89 + 1) * Float.Model.pow2 1073)) (Float.Theory.units x) = True :=
        J
          (v z => Int.leq v (Float.Theory.units x) = True)
          (Float.Theory.unitsMonoKey 89.5.bits x.bits (Float.Theory.leTrans 89.5 89.95 x byComputing near2))
          (byComputing: Float.Theory.units 89.5 = OfNat ((2 * 89 + 1) * Float.Model.pow2 1073))
      let cu :=
        Float.Theory.ceilAtLeast x 89
          (Float.Theory.absBelowOf x 3600.0 9007199254740992.0 byComputing xLo xHi byComputing)
          hu
      let c90: 90.0 <= Float.ceil x :=
        Float.Theory.leOfUnitsPos 90.0
          (Float.ceil x)
          (posOfLeMul (Float.Theory.units (Float.ceil x)) (89 + 1) (Float.Model.pow2 1074) byComputing byComputing cu)
          (J
            (v z => Int.leq v (Float.Theory.units (Float.ceil x)) = True)
            cu
            (byComputing: OfNat ((89 + 1) * Float.Model.pow2 1074) = Float.Theory.units 90.0))
      let r2: 90.0 <= ceilTo x 1.0 :=
        J
          (v z => 90.0 <= v)
          c90
          (ceilToWhole x (Float.Theory.absBelowOf x 360.0 562949953421312.0 byComputing lo hi byComputing)).flipped
      J (st z => 90.0 <= ceilTo x st) r2 e.flipped)

--| The upper edge `to` of a latitude band clamped at 90° is at least the
--| answer, by JS's `<=`: `from` is `90 - width`, `from + width` is above
--| 89.95° (`nearNinety`), and rounding up takes it to at least 90°
--| (`ceilStepAtLeastNinety`), which the answer is at most.
theorem latitudeToAboveClamped ∀ (lat width unit: Float)
    (latHi: lat <= 90.0)
    (fl: Float.isFinite lat = True)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (atTop: Float.min (Float.max (lat - placeAt unit * width) (-90.0)) (90.0 - width) = 90.0 - width):
    Float.ieeeLe lat (latitudeBand lat width (placeAt unit)).to.value = True :=
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let top := topEdgeRange width fw w0 wHi
  let x: Float := 90.0 - width + width
  let r := edgePlusWidth (90.0 - width) width top.right.left top.right.right fw w0 wHi
  let c: Float := ceilTo x (stepFor width)
  let nc: Float.isNaN c = False := notNaNOfFinite c (ceilStepBound x width r.left r.right).left
  let le: lat <= c :=
    Float.Theory.leTrans lat 90.0 c latHi (ceilStepAtLeastNinety x width r.left r.right (nearNinety width wLo wHi))
  J
    (f z => Float.ieeeLe lat (Float.min 90.0 (ceilTo (f + width) (stepFor width))) = True)
    (Float.ieeeLeOfLe lat
      (Float.min 90.0 c)
      (notNaNOfFinite lat fl)
      (Float.minNotNaN 90.0 c byComputing nc)
      (clampToKeeps lat c nc latHi le))
    atTop.flipped

--| A latitude band's upper edge is at least the answer, by JS's `<=`, with
--| the hypotheses of `latitudeFromBelow`: clamped at 90° or not.
theorem latitudeToAbove ∀ (lat width unit: Float)
    (latLo: -90.0 <= lat)
    (latHi: lat <= 90.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    Float.ieeeLe lat (latitudeBand lat width (placeAt unit)).to.value = True :=
  let fl: Float.isFinite lat = True := Float.finiteBetween (-90.0) lat 90.0 byComputing byComputing latLo latHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 180.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let unc: Float := lat - placeAt unit * width
  let nu: Float.isNaN unc = False :=
    notNaNOfFinite unc (unclampedFacts lat width unit latLo latHi wLo wHi low high).left
  Float.Theory.orCase
    (Float.minEither
      (Float.max unc (-90.0))
      (90.0 - width)
      (Float.maxNotNaN unc (-90.0) nu byComputing)
      (notNaNOfFinite (90.0 - width) (topEdgeRange width fw w0 wHi).left))
    (e => latitudeToAboveUnclamped lat width unit latLo latHi wLo wHi low high e)
    (e => latitudeToAboveClamped lat width unit latHi fl wLo wHi e)

--| The answer is in its latitude band, by JS's comparisons, for a latitude
--| within [-90°, 90°], a width from 1e-11° to 180° and `unit` from 0 to 1.
theorem latitudeBandContains ∀ (lat lon width unit: Float)
    (latLo: -90.0 <= lat)
    (latHi: lat <= 90.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 180.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    inHintBand (latitudeBand lat width (placeAt unit)) (point lat lon) = True :=
  Bool.andIntro
    (latitudeFromBelow lat width unit latLo latHi wLo wHi low high)
    (latitudeToAbove lat width unit latLo latHi wLo wHi low high)

--| A band's span, ten tolerances in degrees of arc, is finite and at least
--| 1e-11° for a tolerance from 1.2e-10 km to 20,000 km: `span` is monotone
--| in the tolerance, and ten times 1.2e-10 km is 1.08e-11° (111.19 km to
--| the degree).
theorem spanRange ∀ (tolerance: Float)
    (tolLo: 1.2e-10 <= tolerance)
    (tolHi: tolerance <= 20000.0):
    (Float.isFinite (kmToDegrees (hintWidthTolerances * tolerance)) = True)
      ∧ (1e-11 <= kmToDegrees (hintWidthTolerances * tolerance)) :=
  let ft: Float.isFinite tolerance = True :=
    Float.finiteBetween 1.2e-10 tolerance 20000.0 byComputing byComputing tolLo tolHi
  let k: Float := (earthRadius * pi) / 180.0
  let pos: 0.0 < k := byComputing
  let fk: Float.isFinite k = True := byComputing
  let span: Float := kmToDegrees (hintWidthTolerances * tolerance)
  let a: hintWidthTolerances * 1.2e-10 <= hintWidthTolerances * tolerance :=
    Float.mulMonotone 1.2e-10 tolerance hintWidthTolerances byComputing ft byComputing byComputing tolLo
  let b: hintWidthTolerances * tolerance <= hintWidthTolerances * 20000.0 :=
    Float.mulMonotone tolerance 20000.0 hintWidthTolerances ft byComputing byComputing byComputing tolHi
  let lo: (hintWidthTolerances * 1.2e-10) / k <= span :=
    Float.divMonotone (hintWidthTolerances * 1.2e-10) (hintWidthTolerances * tolerance) k pos fk a
  let hi: span <= (hintWidthTolerances * 20000.0) / k :=
    Float.divMonotone (hintWidthTolerances * tolerance) (hintWidthTolerances * 20000.0) k pos fk b
  Both
    (Float.finiteBetween
      ((hintWidthTolerances * 1.2e-10) / k)
      span
      ((hintWidthTolerances * 20000.0) / k)
      byComputing
      byComputing
      lo
      hi)
    (Float.Theory.leTrans 1e-11 ((hintWidthTolerances * 1.2e-10) / k) span byComputing lo)

--| A latitude band's width, `min span 180`, is from 1e-11° to 180° for a
--| tolerance from 1.2e-10 km to 20,000 km (`spanRange`).
theorem latitudeWidthRange ∀ (tolerance: Float)
    (tolLo: 1.2e-10 <= tolerance)
    (tolHi: tolerance <= 20000.0):
    (1e-11 <= Float.min (kmToDegrees (hintWidthTolerances * tolerance)) 180.0)
      ∧ (Float.min (kmToDegrees (hintWidthTolerances * tolerance)) 180.0 <= 180.0) :=
  let span: Float := kmToDegrees (hintWidthTolerances * tolerance)
  let sr := spanRange tolerance tolLo tolHi
  let ns: Float.isNaN span = False := notNaNOfFinite span sr.left
  Both (Float.leMin span 180.0 1e-11 ns byComputing sr.right byComputing) (Float.minLeRight span 180.0 ns byComputing)

--| A longitude band's width, `min (span / cosLatitude) 120`, is from 1e-11°
--| to 120° for a tolerance from 1.2e-10 km to 20,000 km and a cosine from
--| 1e-17 to 1: dividing by a cosine of at most 1 doesn't shrink the span
--| (`Float.divAntitone`), and the quotient isn't the NaN
--| (`Float.divNotNaN`), so `min` is the smaller of the two.
theorem longitudeWidthRange ∀ (tolerance cosLatitude: Float)
    (tolLo: 1.2e-10 <= tolerance)
    (tolHi: tolerance <= 20000.0)
    (cosLo: 1e-17 <= cosLatitude)
    (cosHi: cosLatitude <= 1.0):
    (1e-11 <= Float.min (kmToDegrees (hintWidthTolerances * tolerance) / cosLatitude) maxLongitudeSpan)
      ∧ (Float.min (kmToDegrees (hintWidthTolerances * tolerance) / cosLatitude) maxLongitudeSpan <= 120.0) :=
  let span: Float := kmToDegrees (hintWidthTolerances * tolerance)
  let sr := spanRange tolerance tolLo tolHi
  let cpos: 0.0 < cosLatitude :=
    Float.Theory.ltLeTrans (Float.orderKey 0.0) (Float.orderKey 1e-17) (Float.orderKey cosLatitude) byComputing cosLo
  let fc: Float.isFinite cosLatitude = True :=
    Float.finiteBetween 1e-17 cosLatitude 1.0 byComputing byComputing cosLo cosHi
  let grow: span / 1.0 <= span / cosLatitude :=
    Float.divAntitone span cosLatitude 1.0 cpos fc byComputing cosHi sr.left
      (Float.Theory.leTrans 0.0 1e-11 span byComputing sr.right)
  let atLeast: 1e-11 <= span / cosLatitude :=
    Float.Theory.leTrans 1e-11 span
      (span / cosLatitude)
      sr.right
      (J (y w => y <= span / cosLatitude) grow (Float.divOneRight span))
  let nq: Float.isNaN (span / cosLatitude) = False := Float.divNotNaN span cosLatitude cpos fc sr.left
  Both
    (Float.leMin (span / cosLatitude) maxLongitudeSpan 1e-11 nq byComputing atLeast byComputing)
    (Float.minLeRight (span / cosLatitude) maxLongitudeSpan nq byComputing)

--| The answer is in its latitude hint band, by JS's comparisons, the TypeScript's
--| `inHintBand(hintBand(answer, tolerance, LATITUDE, unit, …), answer)`.
--| Each hypothesis holds of every real round:
--|
--| - `latLo`, `latHi`: a latitude is within [-90°, 90°].
--| - `tolLo`: the tolerance is at least 1.2e-10 km (0.12 µm), so the band
--|   is at least 1e-11° wide and its 15 % margin outlasts rounding to
--|   tenths (2^-42). Below about 1e-13 km the answer can fall outside
--|   (`narrowLatitudeBandMissesAnswer`, finding 1); a real tolerance is
--|   metres at least.
--| - `tolHi`: the tolerance is at most 20,000 km, half the Earth's
--|   circumference, past which no tolerance means anything; it keeps the
--|   width finite.
--| - `low`, `high`: `unit` is from 0 to 1, as `seededUnit` gives
--|   (`seededUnitInUnit`).
--|
--| `cosLatitude` plays no part in a latitude band.
theorem answerInLatitudeBand ∀ (answer: LatLon) (tolerance: Km) (unit cosLatitude: Float)
    (latLo: -90.0 <= answer.lat.value)
    (latHi: answer.lat.value <= 90.0)
    (tolLo: 1.2e-10 <= tolerance.value)
    (tolHi: tolerance.value <= 20000.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    inHintBand (hintBand answer tolerance Latitude unit cosLatitude) answer = True :=
  let w := latitudeWidthRange tolerance.value tolLo tolHi
  latitudeBandContains answer.lat.value answer.lon.value
    (Float.min (kmToDegrees (hintWidthTolerances * tolerance.value)) 180.0)
    unit
    latLo
    latHi
    w.left
    w.right
    low
    high

-- The answer in its band: longitude

--| A double within 361 · 2^1074 units of zero, short of it, is within 361°.
theorem within361OfUnits ∀ (x: Float)
    (lo: Int.less (Float.Theory.units (-361.0)) (Float.Theory.units x) = True)
    (hi: Int.less (Float.Theory.units x) (Float.Theory.units 361.0) = True):
    (-361.0 <= x) ∧ (x <= 361.0) :=
  Both
    (Float.Theory.leOfUnitsNeg
      (-361.0)
      x
      byComputing
      (Float.Theory.intLeOfLess (Float.Theory.units (-361.0)) (Float.Theory.units x) lo))
    (Float.Theory.leOfUnitsPos x 361.0 byComputing
      (Float.Theory.intLeOfLess (Float.Theory.units x) (Float.Theory.units 361.0) hi))

theorem remainderWithin ∀ (u lo hi a: Int) (d p: Nat)
    (el: lo = Int.neg (OfNat (p * 361)))
    (eh: hi = OfNat (p * 361))
    (ed: Int.natAbs a = p * 360)
    (h: Int.natAbs u < Int.natAbs a):
    (Int.less lo u = True) ∧ (Int.less u hi = True) :=
  Both (arithmetic [el, ed, h]) (arithmetic [eh, ed, h])

theorem turnsDistribute ∀ (t1 t2 u: Int):
    Int.mul (Int.sub (Int.add t1 t2) (OfNat 1)) u = Int.sub (Int.add (Int.mul t1 u) (Int.mul t2 u)) u :=
  algebra

theorem wrapNearArith ∀ (ux us1 ur1 us2 ur2 uw h u nh t1u t2u tu: Int) (w: Nat)
    (n1a: Int.leq (Int.add ux h) (Int.add us1 (OfNat (w * 2))) = True)
    (n1b: Int.leq us1 (Int.add (Int.add ux h) (OfNat (w * 2))) = True)
    (e1: Int.add ur1 t1u = us1)
    (n2a: Int.leq (Int.add ur1 u) (Int.add us2 (OfNat (w * 2))) = True)
    (n2b: Int.leq us2 (Int.add (Int.add ur1 u) (OfNat (w * 2))) = True)
    (e2: Int.add ur2 t2u = us2)
    (n3a: Int.leq (Int.add ur2 nh) (Int.add uw (OfNat (w * 2))) = True)
    (n3b: Int.leq uw (Int.add (Int.add ur2 nh) (OfNat (w * 2))) = True)
    (enh: nh = Int.neg h)
    (dist: tu = Int.sub (Int.add t1u t2u) u):
    (Int.leq uw (Int.add (Int.sub ux tu) (OfNat (w * 6))) = True)
      ∧ (Int.leq (Int.sub ux tu) (Int.add uw (OfNat (w * 6))) = True) :=
  Both
    (arithmetic [n1a, n1b, e1, n2a, n2b, e2, n3a, n3b, enh, dist])
    (arithmetic [n1a, n1b, e1, n2a, n2b, e2, n3a, n3b, enh, dist])

--| `wrap x`, for `x` within 361°, is `x` less a whole number `c` of 360s to
--| within 6 · 2^-44, in exact units: each `%` is exact (`Float.Theory.remStep`) and each
--| of the three sums is within 2^-43 (`sumNear361`). On whole degrees it is
--| exact (`wrapWholeExact`); on tenths it isn't (`wrapTenth`, finding 2),
--| and this bound is what a narrow band's margin has to outlast.
theorem wrapNear ∀ (x: Float)
    (lo: -361.0 <= x)
    (hi: x <= 361.0)
    [goal: Prop]
    (k: ∀ (c: Int) => Int.leq
      (Float.Theory.units (wrap x))
      (Int.add
        (Int.sub (Float.Theory.units x) (Int.mul c (Float.Theory.units 360.0)))
        (OfNat (Float.Model.pow2 1030 * 6)))
      = True
      → Int.leq
        (Int.sub (Float.Theory.units x) (Int.mul c (Float.Theory.units 360.0)))
        (Int.add (Float.Theory.units (wrap x)) (OfNat (Float.Model.pow2 1030 * 6)))
        = True
      → goal):
    goal :=
  let n1 := sumNear361 x 180.0 lo hi byComputing byComputing
  Float.Theory.remStep (x + 180.0) 360.0 n1.left byComputing byComputing (t1 e1 a1 g1 =>
    let r1: Float := (x + 180.0) % 360.0
    let w1 :=
      remainderWithin
        (Float.Theory.units r1)
        (Float.Theory.units (-361.0))
        (Float.Theory.units 361.0)
        (Float.Theory.units 360.0)
        0
        (Float.Model.pow2 1074)
        byComputing
        byComputing
        byComputing
        a1
    let b1 := within361OfUnits r1 w1.left w1.right
    let n2 := sumNear361 r1 360.0 b1.left b1.right byComputing byComputing
    Float.Theory.remStep (r1 + 360.0) 360.0 n2.left byComputing byComputing (t2 e2 a2 g2 =>
      let r2: Float := (r1 + 360.0) % 360.0
      let w2 :=
        remainderWithin
          (Float.Theory.units r2)
          (Float.Theory.units (-361.0))
          (Float.Theory.units 361.0)
          (Float.Theory.units 360.0)
          0
          (Float.Model.pow2 1074)
          byComputing
          byComputing
          byComputing
          a2
      let b2 := within361OfUnits r2 w2.left w2.right
      let n3 := sumNear361 r2 (-180.0) b2.left b2.right byComputing byComputing
      let e3: r2 + -180.0 = wrap x := (Float.subAddNeg r2 180.0).flipped
      let n3a: Int.leq
        (Int.add (Float.Theory.units r2) (Float.Theory.units (-180.0)))
        (Int.add (Float.Theory.units (wrap x)) (OfNat (Float.Model.pow2 1030 * 2)))
        = True :=
        J
          (y z =>
            Int.leq
              (Int.add (Float.Theory.units r2) (Float.Theory.units (-180.0)))
              (Int.add (Float.Theory.units y) (OfNat (Float.Model.pow2 1030 * 2)))
              = True)
          n3.right.left
          e3
      let n3b: Int.leq
        (Float.Theory.units (wrap x))
        (Int.add (Int.add (Float.Theory.units r2) (Float.Theory.units (-180.0))) (OfNat (Float.Model.pow2 1030 * 2)))
        = True :=
        J
          (y z =>
            Int.leq
              (Float.Theory.units y)
              (Int.add
                (Int.add (Float.Theory.units r2) (Float.Theory.units (-180.0)))
                (OfNat (Float.Model.pow2 1030 * 2)))
              = True)
          n3.right.right
          e3
      let c: Int := Int.sub (Int.add t1 t2) (OfNat 1)
      let r :=
        wrapNearArith
          (Float.Theory.units x)
          (Float.Theory.units (x + 180.0))
          (Float.Theory.units r1)
          (Float.Theory.units (r1 + 360.0))
          (Float.Theory.units r2)
          (Float.Theory.units (wrap x))
          (Float.Theory.units 180.0)
          (Float.Theory.units 360.0)
          (Float.Theory.units (-180.0))
          (Int.mul t1 (Float.Theory.units 360.0))
          (Int.mul t2 (Float.Theory.units 360.0))
          (Int.mul c (Float.Theory.units 360.0))
          (Float.Model.pow2 1030)
          n1.right.left
          n1.right.right
          e1
          n2.right.left
          n2.right.right
          e2
          n3a
          n3b
          byComputing
          (turnsDistribute t1 t2 (Float.Theory.units 360.0))
      k c r.left r.right))

--| A whole number of turns `c · d` strictly between `-2d` and `2d` is `-d`, 0 or `d`.
theorem turnTimes ∀ (c: Int) (d: Nat)
    (lo: Int.less (Int.neg (OfNat (d * 2))) (Int.mul c (OfNat d)) = True)
    (hi: Int.less (Int.mul c (OfNat d)) (OfNat (d * 2)) = True):
    (Int.mul c (OfNat d) = Int.neg (OfNat d)) ∨ ((Int.mul c (OfNat d) = OfNat 0) ∨ (Int.mul c (OfNat d) = OfNat d)) :=
  match c with
    | OfNat j =>
      match j with
        | Zero => Inr (Inl algebra)
        | Succ Zero => Inr (Inr algebra)
        | Succ (Succ n) =>
          let e: Int.mul (OfNat (Succ (Succ n))) (OfNat d) = OfNat (Succ (Succ n) * d) :=
            Float.Theory.intMulOfNat (Succ (Succ n)) d
          let big: 2 * d ≤ Succ (Succ n) * d := Nat.leMulRight 2 (Succ (Succ n)) d (arithmetic)
          Void.impossible (arithmetic [hi, e, big])
    | NegSucc j =>
      match j with
        | Zero => Inl algebra
        | Succ n =>
          let e := Float.Theory.intMulNegSucc (Succ n) d
          let big: 2 * d ≤ (Succ n + 1) * d := Nat.leMulRight 2 (Succ n + 1) d (arithmetic)
          Void.impossible (arithmetic [lo, e, big])

--| Where the wrapped edges `F` and `T` fall against the answer `l`, in
--| exact units: either `F ≤ l ≤ T` with neither wrapped across ±180°, or
--| the band crosses ±180°, `T < F`, and the answer is on one side. `F` is
--| the lower edge `a` less `mA` (a whole number of turns `u`) to within
--| 6 · 2^-44 (`wrapNear`), `T` likewise; `a` is more than 6 · 2^-44 below
--| `l` and `b` as far above, and the band is under a turn wide.
theorem longitudeCases ∀ (ua ub ul uF uT mA mB h u: Int) (w: Nat)
    (hu: u = Int.add h h)
    (small: Int.less (OfNat (w * 12)) h = True)
    (fA: Int.leq uF (Int.add (Int.sub ua mA) (OfNat (w * 6))) = True)
    (gA: Int.leq (Int.sub ua mA) (Int.add uF (OfNat (w * 6))) = True)
    (fB: Int.leq uT (Int.add (Int.sub ub mB) (OfNat (w * 6))) = True)
    (gB: Int.leq (Int.sub ub mB) (Int.add uT (OfNat (w * 6))) = True)
    (fLo: Int.leq (Int.neg h) uF = True)
    (fHi: Int.leq uF h = True)
    (tLo: Int.leq (Int.neg h) uT = True)
    (tHi: Int.leq uT h = True)
    (lLo: Int.leq (Int.neg h) ul = True)
    (lHi: Int.leq ul h = True)
    (aBelow: Int.less (Int.add ua (OfNat (w * 6))) ul = True)
    (bAbove: Int.less (Int.add ul (OfNat (w * 6))) ub = True)
    (narrow: Int.less (Int.add ub (OfNat (w * 12))) (Int.add ua u) = True)
    (aLow: Int.less (Int.neg u) ua = True)
    (bHigh: Int.less ub u = True)
    (tA: (mA = Int.neg u) ∨ ((mA = OfNat 0) ∨ (mA = u)))
    (tB: (mB = Int.neg u) ∨ ((mB = OfNat 0) ∨ (mB = u))):
    ((Int.less uF ul = True) ∧ (Int.less ul uT = True))
      ∨ (((Int.less uT uF = True) ∧ (Int.less ul uT = True)) ∨ ((Int.less uT uF = True) ∧ (Int.less uF ul = True))) :=
  Float.Theory.orCase tA
    (a1 =>
      Float.Theory.orCase tB
        (b1 => Void.impossible (arithmetic [hu, small, fA, gA, fB, gB, fHi, tLo, tHi, lLo, aBelow, bAbove, a1, b1]))
        (rest =>
          Float.Theory.orCase rest
            (b0 =>
              Inr
                (Inl
                  (Both
                    (arithmetic [hu, small, fA, gA, fB, gB, narrow, a1, b0])
                    (arithmetic [hu, small, fB, gB, bAbove, b0]))))
            (b2 => Void.impossible (arithmetic [hu, small, fA, gA, fB, gB, fHi, tLo, narrow, a1, b2]))))
    (rest =>
      Float.Theory.orCase rest
        (a0 =>
          Float.Theory.orCase tB (b1 => Void.impossible (arithmetic [hu, small, gB, tHi, lLo, bAbove, b1])) (rest2 =>
            Float.Theory.orCase rest2
              (b0 => Inl (Both (arithmetic [hu, small, fA, aBelow, a0]) (arithmetic [hu, small, gB, bAbove, b0])))
              (b2 =>
                Inr
                  (Inr
                    (Both
                      (arithmetic [hu, small, fA, gA, fB, gB, narrow, a0, b2])
                      (arithmetic [hu, small, fA, aBelow, a0]))))))
        (a2 => Void.impossible (arithmetic [hu, small, gA, fLo, lHi, aBelow, a2])))

--| `turnTimes` for a turn `u` given as an equation.
theorem turnTimesOf ∀ (c u: Int) (d: Nat)
    (eu: u = OfNat d)
    (lo: Int.less (Int.neg (Int.add u u)) (Int.mul c u) = True)
    (hi: Int.less (Int.mul c u) (Int.add u u) = True):
    (Int.mul c u = Int.neg u) ∨ ((Int.mul c u = OfNat 0) ∨ (Int.mul c u = u)) :=
  let step: Int.less (Int.neg (Int.add u u)) (Int.mul c u) = True
    → Int.less (Int.mul c u) (Int.add u u) = True
    → (Int.mul c u = Int.neg u) ∨ ((Int.mul c u = OfNat 0) ∨ (Int.mul c u = u)) :=
    J
      (v z =>
        Int.less (Int.neg (Int.add v v)) (Int.mul c v) = True
          → Int.less (Int.mul c v) (Int.add v v) = True
          → (Int.mul c v = Int.neg v) ∨ ((Int.mul c v = OfNat 0) ∨ (Int.mul c v = v)))
      (lo2 hi2 => turnTimes c d (arithmetic [lo2]) (arithmetic [hi2]))
      eu.flipped
  step lo hi

--| The turns `wrap` takes off an edge within a turn of 0, landing in
--| [-180°, 180°], are fewer than two either way.
theorem turnBounds ∀ (x uF m h u: Int) (w: Nat)
    (hu: u = Int.add h h)
    (small: Int.less (OfNat (w * 12)) h = True)
    (f: Int.leq uF (Int.add (Int.sub x m) (OfNat (w * 6))) = True)
    (g: Int.leq (Int.sub x m) (Int.add uF (OfNat (w * 6))) = True)
    (fLo: Int.leq (Int.neg h) uF = True)
    (fHi: Int.leq uF h = True)
    (xLo: Int.less (Int.neg u) x = True)
    (xHi: Int.less x u = True):
    (Int.less (Int.neg (Int.add u u)) m = True) ∧ (Int.less m (Int.add u u) = True) :=
  Both (arithmetic [hu, small, f, g, fLo, fHi, xLo, xHi]) (arithmetic [hu, small, f, g, fLo, fHi, xLo, xHi])

--| The unrounded edges of a longitude band against the answer, in exact
--| units, from the margins, the rounding at the step, and the coarse
--| bounds on rounding (each edge moves at most 2° outwards).
theorem longitudeEdgeArith ∀ (ua ub ul uf ufw uw u2 u120 um300 h u u361 um361: Int) (w: Nat)
    (fsA: Int.leq ua (Int.add uf (OfNat (w * 4))) = True)
    (mb: Int.less (Int.add uf (OfNat (w * 10))) ul = True)
    (csB: Int.leq ufw (Int.add ub (OfNat (w * 4))) = True)
    (ma: Int.less (Int.add ul (OfNat (w * 10))) ufw = True)
    (fc: Int.leq uf (Int.add ua u2) = True)
    (cc: Int.leq ub (Int.add ufw u2) = True)
    (sw: Int.leq ufw (Int.add (Int.add uf uw) (OfNat (w * 2))) = True)
    (uwHi: Int.leq uw u120 = True)
    (ufLo: Int.leq um300 uf = True)
    (ulLo: Int.leq (Int.neg h) ul = True)
    (ulHi: Int.leq ul h = True)
    (k1: Int.less (Int.add (Int.add (Int.add u2 u2) u120) (OfNat (w * 14))) u = True)
    (k2: Int.less (Int.neg u) (Int.sub um300 u2) = True)
    (k3: Int.less (Int.add (Int.add (Int.add h u120) u2) (OfNat (w * 2))) u = True)
    (k4: Int.less um361 (Int.sub um300 u2) = True)
    (k5: Int.less h u361 = True)
    (k6: Int.less um361 (Int.neg h) = True)
    (k7: Int.less (Int.add (Int.add (Int.add h u120) u2) (OfNat (w * 2))) u361 = True):
    ((Int.less (Int.add ua (OfNat (w * 6))) ul = True) ∧ (Int.less (Int.add ul (OfNat (w * 6))) ub = True))
      ∧ (((Int.less (Int.add ub (OfNat (w * 12))) (Int.add ua u) = True)
        ∧ ((Int.less (Int.neg u) ua = True) ∧ (Int.less ub u = True)))
        ∧ (((Int.less um361 ua = True) ∧ (Int.less ua u361 = True))
          ∧ ((Int.less um361 ub = True) ∧ (Int.less ub u361 = True)))) :=
  Both
    (Both (arithmetic [fsA, mb]) (arithmetic [csB, ma]))
    (Both
      (Both
        (arithmetic [fc, cc, sw, uwHi, k1])
        (Both (arithmetic [fc, ufLo, k2]) (arithmetic [cc, sw, uwHi, mb, fsA, fc, ulHi, k3])))
      (Both
        (Both (arithmetic [fc, ufLo, k4]) (arithmetic [fsA, mb, ulHi, k5]))
        (Both (arithmetic [csB, ma, ulLo, k6]) (arithmetic [cc, sw, uwHi, mb, ulHi, k7]))))

theorem belowTurn ∀ (ua ul h u: Int) (w: Nat)
    (a: Int.less (Int.add ua (OfNat (w * 6))) ul = True)
    (lh: Int.leq ul h = True)
    (hu: u = Int.add h h)
    (small: Int.less (OfNat (w * 12)) h = True):
    Int.less ua u = True :=
  arithmetic [a, lh, hu, small]

theorem aboveNegTurn ∀ (ub ul h u: Int) (w: Nat)
    (b: Int.less (Int.add ul (OfNat (w * 6))) ub = True)
    (lh: Int.leq (Int.neg h) ul = True)
    (hu: u = Int.add h h)
    (small: Int.less (OfNat (w * 12)) h = True):
    Int.less (Int.neg u) ub = True :=
  arithmetic [b, lh, hu, small]

--| Doubles other than the NaN with units in strict order are in JS's order.
theorem ieeeLeOfUnitsLess ∀ (x y: Float)
    (nx: Float.isNaN x = False)
    (ny: Float.isNaN y = False)
    (h: Int.less (Float.Theory.units x) (Float.Theory.units y) = True):
    Float.ieeeLe x y = True :=
  Float.ieeeLeOfLe x y nx ny (floatLeOfLt x y (Float.Theory.lessOfUnits x y h))

--| With `y`'s units below `x`'s, JS's `x <= y` is false.
theorem notIeeeLeOfUnits ∀ (x y: Float)
    (h: Int.less (Float.Theory.units y) (Float.Theory.units x) = True):
    Float.ieeeLe x y = False :=
  match e: Float.ieeeLe x y with
    | False => byComputing
    | True =>
      Void.impossible
        (Float.Theory.orCase
          (Float.leOfIeeeLe x y e)
          (le => arithmetic [Float.Theory.unitsMonoKey x.bits y.bits le, h])
          (zz => arithmetic [Float.Theory.unitsZero x zz.left, Float.Theory.unitsZero y zz.right, h]))

--| `inHintBand`'s reading of a longitude band, from `longitudeCases`: a
--| band that doesn't cross ±180° contains the answer between its edges, and
--| one that does has `from > to` and the answer on one side.
theorem inLongitudeOfCases ∀ (from to lon: Float)
    (nf: Float.isNaN from = False)
    (nt: Float.isNaN to = False)
    (nl: Float.isNaN lon = False)
    (sides: ((Int.less (Float.Theory.units from) (Float.Theory.units lon) = True)
      ∧ (Int.less (Float.Theory.units lon) (Float.Theory.units to) = True))
      ∨ (((Int.less (Float.Theory.units to) (Float.Theory.units from) = True)
        ∧ (Int.less (Float.Theory.units lon) (Float.Theory.units to) = True))
        ∨ ((Int.less (Float.Theory.units to) (Float.Theory.units from) = True)
          ∧ (Int.less (Float.Theory.units from) (Float.Theory.units lon) = True)))):
    (if Float.ieeeLe from to then Float.ieeeLe from lon ∧ Float.ieeeLe lon to
     else Float.ieeeLe from lon ∨ Float.ieeeLe lon to)
      = True :=
  Float.Theory.orCase sides
    (c =>
      let below := ieeeLeOfUnitsLess from lon nf nl c.left
      let above := ieeeLeOfUnitsLess lon to nl nt c.right
      match e: Float.ieeeLe from to with
        | True => Bool.andIntro below above
        | False => Bool.orLeft below)
    (rest =>
      Float.Theory.orCase rest
        (c => rewrite notIeeeLeOfUnits from to c.left then Bool.orRight (ieeeLeOfUnitsLess lon to nl nt c.right))
        (c => rewrite notIeeeLeOfUnits from to c.left then Bool.orLeft (ieeeLeOfUnitsLess from lon nf nl c.right)))

--| A longitude band's unrounded lower edge, `lon - placeAt unit * width`, is
--| finite and from -300° to 180°.
theorem longitudeFromRange ∀ (lon width unit: Float)
    (lonLo: -180.0 <= lon)
    (lonHi: lon <= 180.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 120.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    (Float.isFinite (lon - placeAt unit * width) = True)
      ∧ ((-300.0 <= lon - placeAt unit * width) ∧ (lon - placeAt unit * width <= 180.0)) :=
  let from: Float := lon - placeAt unit * width
  let fl: Float.isFinite lon = True := Float.finiteBetween (-180.0) lon 180.0 byComputing byComputing lonLo lonHi
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 120.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let row := marginRow lon width unit fl fw w0 low high
  let s85 := shareOfWidth 0.85 width byComputing byComputing fw w0
  let a: -180.0 - 0.85 * width <= lon - 0.85 * width :=
    Float.subMonotoneLeft (-180.0) lon (0.85 * width) byComputing fl s85.left lonLo
  let b: -180.0 - 120.0 <= -180.0 - 0.85 * width :=
    Float.subAntitoneRight
      (-180.0)
      (0.85 * width)
      120.0
      byComputing
      s85.left
      byComputing
      (Float.Theory.leTrans (0.85 * width) width 120.0 s85.right.right wHi)
  let lo: -300.0 <= from :=
    J
      (y z => y <= from)
      (Float.Theory.leTrans
        (-180.0 - 120.0)
        (lon - 0.85 * width)
        from
        (Float.Theory.leTrans (-180.0 - 120.0) (-180.0 - 0.85 * width) (lon - 0.85 * width) b a)
        row.left)
      (byComputing: -180.0 - 120.0 = -300.0)
  let lt: from < lon :=
    Float.Theory.lessOfUnits from lon
      (lessOfAddNat
        (Float.Theory.units from)
        (Float.Theory.units lon)
        (Float.Model.pow2 1030 * 10)
        (marginBelowExact lon width unit
          (Float.Theory.leTrans (-361.0) (-180.0) lon byComputing lonLo)
          (Float.Theory.leTrans lon 180.0 361.0 lonHi byComputing)
          wLo
          (Float.Theory.leTrans width 120.0 361.0 wHi byComputing)
          low
          high))
  let hi: from <= 180.0 := Float.Theory.leTrans from lon 180.0 (floatLeOfLt from lon lt) lonHi
  Both (Float.finiteBetween (-300.0) from 180.0 byComputing byComputing lo hi) (Both lo hi)

--| An edge from -300° to 180° plus a width from 0 to 120° is within 360°.
theorem lonEdgePlusWidth ∀ (from width: Float)
    (fromLo: -300.0 <= from)
    (fromHi: from <= 180.0)
    (fw: Float.isFinite width = True)
    (w0: 0.0 <= width)
    (wHi: width <= 120.0):
    (-360.0 <= from + width) ∧ (from + width <= 360.0) :=
  let ff: Float.isFinite from = True := Float.finiteBetween (-300.0) from 180.0 byComputing byComputing fromLo fromHi
  let lo: -300.0 + 0.0 <= from + width :=
    Float.Theory.leTrans
      (-300.0 + 0.0)
      (from + 0.0)
      (from + width)
      (Float.addMonotoneLeft (-300.0) from 0.0 byComputing ff byComputing fromLo)
      (Float.addMonotone 0.0 width from byComputing fw ff w0)
  let hi: from + width <= 180.0 + 120.0 :=
    Float.Theory.leTrans
      (from + width)
      (180.0 + width)
      (180.0 + 120.0)
      (Float.addMonotoneLeft from 180.0 width ff byComputing fw fromHi)
      (Float.addMonotone width 120.0 180.0 fw byComputing byComputing wHi)
  Both
    (Float.Theory.leTrans (-360.0) (-300.0 + 0.0) (from + width) byComputing lo)
    (Float.Theory.leTrans (from + width) (180.0 + 120.0) 360.0 hi byComputing)

--| The answer is in its longitude band, by JS's comparisons and the band's
--| wrapped reading (`from > to` is `[from, 180) ∪ [-180, to]`), for a
--| longitude in [-180°, 180°), a width from 1e-11° to 120° and `unit` from
--| 0 to 1. Rounding at the band's step moves an edge outwards by at most
--| 2° (`floorCoarse`, `ceilCoarse`), which keeps the rounded band under a
--| turn wide.
--|
--| The proof: the unrounded edges are more than 10 · 2^-44 from the answer
--| (`marginBelowExact`, `marginAboveExact`), rounding takes off at most
--| 4 · 2^-44 (`floorStepBound`, `ceilStepBound`), and `wrap` moves each by
--| whole turns to within 6 · 2^-44 (`wrapNear`), so no band needs `wrap`
--| to be exact on tenths (finding 2). `longitudeCases` sorts out which
--| turns, and `inLongitudeOfCases` reads the result as `inHintBand` does.
theorem longitudeBandContains ∀ (lat lon width unit: Float)
    (lonLo: -180.0 <= lon)
    (lonHi: lon < 180.0)
    (wLo: 1e-11 <= width)
    (wHi: width <= 120.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0):
    inHintBand (longitudeBand lon width (placeAt unit)) (point lat lon) = True :=
  let lonLe: lon <= 180.0 := floatLeOfLt lon 180.0 lonHi
  let fl: Float.isFinite lon = True := Float.finiteBetween (-180.0) lon 180.0 byComputing byComputing lonLo lonLe
  let nl: Float.isNaN lon = False := notNaNOfFinite lon fl
  let fw: Float.isFinite width = True := Float.finiteBetween 1e-11 width 120.0 byComputing byComputing wLo wHi
  let w0: 0.0 <= width := Float.Theory.leTrans 0.0 1e-11 width byComputing wLo
  let from: Float := lon - placeAt unit * width
  let fr := longitudeFromRange lon width unit lonLo lonLe wLo wHi low high
  let fromLo: -360.0 <= from := Float.Theory.leTrans (-360.0) (-300.0) from byComputing fr.right.left
  let fromHi: from <= 360.0 := Float.Theory.leTrans from 180.0 360.0 fr.right.right byComputing
  let step: Float := stepFor width
  let a: Float := floorTo from step
  let fs := floorStepBound from width fromLo fromHi
  let r := lonEdgePlusWidth from width fr.right.left fr.right.right fw w0 wHi
  let b: Float := ceilTo (from + width) step
  let cs := ceilStepBound (from + width) width r.left r.right
  let sw :=
    sumNear361 from width
      (Float.Theory.leTrans (-361.0) (-300.0) from byComputing fr.right.left)
      (Float.Theory.leTrans from 180.0 361.0 fr.right.right byComputing)
      (Float.Theory.leTrans (-361.0) 0.0 width byComputing w0)
      (Float.Theory.leTrans width 120.0 361.0 wHi byComputing)
  let negOneEighty: Float.Theory.units (-180.0) = Int.neg (Float.Theory.units 180.0) := byComputing
  let e :=
    longitudeEdgeArith
      (Float.Theory.units a)
      (Float.Theory.units b)
      (Float.Theory.units lon)
      (Float.Theory.units from)
      (Float.Theory.units (from + width))
      (Float.Theory.units width)
      (Float.Theory.units 2.0)
      (Float.Theory.units 120.0)
      (Float.Theory.units (-300.0))
      (Float.Theory.units 180.0)
      (Float.Theory.units 360.0)
      (Float.Theory.units 361.0)
      (Float.Theory.units (-361.0))
      (Float.Model.pow2 1030)
      (J
        (q z => Int.leq (Float.Theory.units a) (Int.add (Float.Theory.units from) (OfNat q)) = True)
        fs.right
        (byComputing: Float.Model.pow2 1032 = Float.Model.pow2 1030 * 4))
      (marginBelowExact lon width unit
        (Float.Theory.leTrans (-361.0) (-180.0) lon byComputing lonLo)
        (Float.Theory.leTrans lon 180.0 361.0 lonLe byComputing)
        wLo
        (Float.Theory.leTrans width 120.0 361.0 wHi byComputing)
        low
        high)
      (J
        (q z => Int.leq (Float.Theory.units (from + width)) (Int.add (Float.Theory.units b) (OfNat q)) = True)
        cs.right
        (byComputing: Float.Model.pow2 1032 = Float.Model.pow2 1030 * 4))
      (marginAboveExact lon width unit lonLo lonLe wLo
        (Float.Theory.leTrans width 120.0 180.0 wHi byComputing)
        low
        high)
      (floorCoarse width from fromLo fromHi)
      (ceilCoarse width (from + width) r.left r.right)
      sw.right.right
      (Float.Theory.unitsMonoKey width.bits 120.0.bits wHi)
      (Float.Theory.unitsMonoKey (-300.0).bits from.bits fr.right.left)
      (J
        (q z => Int.leq q (Float.Theory.units lon) = True)
        (Float.Theory.unitsMonoKey (-180.0).bits lon.bits lonLo)
        negOneEighty)
      (Float.Theory.unitsMonoKey lon.bits 180.0.bits lonLe)
      byComputing
      byComputing
      byComputing
      byComputing
      byComputing
      byComputing
      byComputing
  let aIn := within361OfUnits a e.right.right.left.left e.right.right.left.right
  let bIn := within361OfUnits b e.right.right.right.left e.right.right.right.right
  let fa: Float.isFinite a = True := Float.finiteBetween (-361.0) a 361.0 byComputing byComputing aIn.left aIn.right
  let fb: Float.isFinite b = True := Float.finiteBetween (-361.0) b 361.0 byComputing byComputing bIn.left bIn.right
  let ra := wrapRange a fa
  let rb := wrapRange b fb
  let nF: Float.isNaN (wrap a) = False :=
    notNaNOfFinite
      (wrap a)
      (Float.finiteBetween
        (-180.0)
        (wrap a)
        180.0
        byComputing
        byComputing
        ra.left
        (floatLeOfLt (wrap a) 180.0 ra.right))
  let nT: Float.isNaN (wrap b) = False :=
    notNaNOfFinite
      (wrap b)
      (Float.finiteBetween
        (-180.0)
        (wrap b)
        180.0
        byComputing
        byComputing
        rb.left
        (floatLeOfLt (wrap b) 180.0 rb.right))
  wrapNear a aIn.left aIn.right (ca fA gA =>
    wrapNear b bIn.left bIn.right (cb fB gB =>
      let u: Int := Float.Theory.units 360.0
      let h: Int := Float.Theory.units 180.0
      let uSum: u = Int.add h h := byComputing
      let hBig: Int.less (OfNat (Float.Model.pow2 1030 * 12)) h = True := byComputing
      let fLo: Int.leq (Int.neg h) (Float.Theory.units (wrap a)) = True :=
        J
          (q z => Int.leq q (Float.Theory.units (wrap a)) = True)
          (Float.Theory.unitsMonoKey (-180.0).bits (wrap a).bits ra.left)
          negOneEighty
      let fHi: Int.leq (Float.Theory.units (wrap a)) h = True :=
        Float.Theory.unitsMonoKey (wrap a).bits 180.0.bits (floatLeOfLt (wrap a) 180.0 ra.right)
      let tLo: Int.leq (Int.neg h) (Float.Theory.units (wrap b)) = True :=
        J
          (q z => Int.leq q (Float.Theory.units (wrap b)) = True)
          (Float.Theory.unitsMonoKey (-180.0).bits (wrap b).bits rb.left)
          negOneEighty
      let tHi: Int.leq (Float.Theory.units (wrap b)) h = True :=
        Float.Theory.unitsMonoKey (wrap b).bits 180.0.bits (floatLeOfLt (wrap b) 180.0 rb.right)
      let tbA :=
        turnBounds
          (Float.Theory.units a)
          (Float.Theory.units (wrap a))
          (Int.mul ca u)
          h
          u
          (Float.Model.pow2 1030)
          uSum
          hBig
          fA
          gA
          fLo
          fHi
          e.right.left.right.left
          (belowTurn
            (Float.Theory.units a)
            (Float.Theory.units lon)
            h
            u
            (Float.Model.pow2 1030)
            e.left.left
            (Float.Theory.unitsMonoKey lon.bits 180.0.bits lonLe)
            uSum
            hBig)
      let tbB :=
        turnBounds
          (Float.Theory.units b)
          (Float.Theory.units (wrap b))
          (Int.mul cb u)
          h
          u
          (Float.Model.pow2 1030)
          uSum
          hBig
          fB
          gB
          tLo
          tHi
          (aboveNegTurn
            (Float.Theory.units b)
            (Float.Theory.units lon)
            h
            u
            (Float.Model.pow2 1030)
            e.left.right
            (J
              (q z => Int.leq q (Float.Theory.units lon) = True)
              (Float.Theory.unitsMonoKey (-180.0).bits lon.bits lonLo)
              negOneEighty)
            uSum
            hBig)
          e.right.left.right.right
      inLongitudeOfCases
        (wrap a)
        (wrap b)
        lon
        nF
        nT
        nl
        (longitudeCases
          (Float.Theory.units a)
          (Float.Theory.units b)
          (Float.Theory.units lon)
          (Float.Theory.units (wrap a))
          (Float.Theory.units (wrap b))
          (Int.mul ca u)
          (Int.mul cb u)
          h
          u
          (Float.Model.pow2 1030)
          uSum
          hBig
          fA
          gA
          fB
          gB
          fLo
          fHi
          tLo
          tHi
          (J
            (q z => Int.leq q (Float.Theory.units lon) = True)
            (Float.Theory.unitsMonoKey (-180.0).bits lon.bits lonLo)
            negOneEighty)
          (Float.Theory.unitsMonoKey lon.bits 180.0.bits lonLe)
          e.left.left
          e.left.right
          e.right.left.left
          e.right.left.right.left
          e.right.left.right.right
          (turnTimesOf ca u (Int.natAbs u) byComputing tbA.left tbA.right)
          (turnTimesOf cb u (Int.natAbs u) byComputing tbB.left tbB.right))))

-- The answer in its band

--| The answer is in its hint band, either axis, by JS's comparisons: the
--| TypeScript's `inHintBand(hintBand(answer, tolerance, axis, unit,
--| cosLatitude), answer)` is true. The hypotheses:
--|
--| - `latLo`, `latHi`, `lonLo`, `lonHi`: the answer is a real place, with
--|   latitude in [-90°, 90°] and longitude in [-180°, 180°), as Whereabouts
--|   stores them (`wrap`'s range).
--| - `tolLo`, `tolHi`: the tolerance is from 1.2e-10 km to 20,000 km (see
--|   `answerInLatitudeBand`); below about 1e-13 km the answer can fall
--|   outside (finding 1).
--| - `low`, `high`: `unit` is from 0 to 1, as `seededUnit` gives.
--| - `cosLo`, `cosHi`: `cosLatitude` is from 1e-17 to 1. The caller passes
--|   `Math.cos` of the answer's latitude in radians, within ±π/2; the
--|   double nearest π/2 is a little below it, so the cosine is at least
--|   about 6.1e-17 (`Math.cos(Math.PI / 2)`), and at most 1. It keeps the
--|   longitude band's width, `min (span / cosLatitude) 120`, from 1e-11°
--|   to 120° (`longitudeWidthRange`). A latitude band ignores it.
theorem answerInBand ∀ (answer: LatLon) (tolerance: Km) (axis: HintAxis) (unit cosLatitude: Float)
    (latLo: -90.0 <= answer.lat.value)
    (latHi: answer.lat.value <= 90.0)
    (lonLo: -180.0 <= answer.lon.value)
    (lonHi: answer.lon.value < 180.0)
    (tolLo: 1.2e-10 <= tolerance.value)
    (tolHi: tolerance.value <= 20000.0)
    (low: 0.0 <= unit)
    (high: unit <= 1.0)
    (cosLo: 1e-17 <= cosLatitude)
    (cosHi: cosLatitude <= 1.0):
    inHintBand (hintBand answer tolerance axis unit cosLatitude) answer = True :=
  match axis with
    | Latitude => answerInLatitudeBand answer tolerance unit cosLatitude latLo latHi tolLo tolHi low high
    | Longitude =>
      let width: Float := Float.min (kmToDegrees (hintWidthTolerances * tolerance.value) / cosLatitude) maxLongitudeSpan
      let w := longitudeWidthRange tolerance.value cosLatitude tolLo tolHi cosLo cosHi
      longitudeBandContains answer.lat.value answer.lon.value width unit lonLo lonHi w.left w.right low high
