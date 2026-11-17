--| What is proved about hint bands, and what is settled by computing.
--| std's float laws (std/Float/Theory.sw) cover `seededUnit`; NOTES.md
--| lists the laws the other band theorems still need.

namespace Whereabouts.Hints.Proofs
import Whereabouts.Hints (..)
import Std (Bool, Float, Int, List, Nat)

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

--| A tenth of a degree, `r / 10`, as `floorTo` and `ceilTo` give one.
def tenth (r: Int): Float := Float.ofInt r / 10.0

--| `describeHint`'s rounding to tenths leaves every tenth from -180° to 180°
--| as it is, so the label of an edge that is a tenth is that edge.
theorem tenthsKeepTheirLabel: (List.range 0 3601).all (k =>
      Float.round (tenth (OfNat k - 1800) * 10.0) / 10.0 == tenth (OfNat k - 1800))
      = True :=
  byComputing
