--| What is proved about hint bands, and what is settled by computing.
--| std's float laws (std/Float/Theory.sw) cover `seededUnit`; NOTES.md
--| lists the laws the other band theorems still need.

namespace Whereabouts.Hints.Proofs
import Whereabouts.Hints (..)
import Std (Float, Int, List, Nat)

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

--| A tenth of a degree, `r / 10`, as `floorTo` and `ceilTo` give one.
def tenth (r: Int): Float := Float.ofInt r / 10.0

--| `describeHint`'s rounding to tenths leaves every tenth from -180° to 180°
--| as it is, so the label of an edge that is a tenth is that edge.
theorem tenthsKeepTheirLabel: (List.range 0 3601).all (k =>
      Float.round (tenth (OfNat k - 1800) * 10.0) / 10.0 == tenth (OfNat k - 1800))
      = True :=
  byComputing
