--| General lemmas the day's proofs use: wrapping one tile at a time is
--| `Int.modNat`, and iterating a wrapped step is wrapping the sum.

namespace Aoc.Year2024.Day14.Proofs
import Std (Bool, DecEq, Eq, Int, List, Nat, Option, Void)

--| A step that adds `distance` and wraps, taken `times` times, adds
--| `times * distance` and wraps.
theorem iterateWrap ∀ (size: Nat) (distance: Int) (step: Nat → Nat)
    (wraps: ∀ (x: Nat) => x < size → step x = Int.modNat (x.toInt + distance) size) (times x: Nat)
    (inside: x < size):
    times.iterate step x = Int.modNat (x.toInt + times.toInt * distance) size :=
  match times with
    | Zero => rewrite (ring: x.toInt + Nat.toInt 0 * distance = x.toInt) in Eq.sym (Int.modNatOfLt size x inside)
    | Succ times =>
      let ok: size ≠ 0 := omega
      let stepInside: step x < size := rewrite wraps x inside in Int.modNatLt (x.toInt + distance) size [ok := ok]
      rewrite iterateWrap size distance step wraps times (step x) stepInside, wraps x inside, Int.modNatModAdd
        (x.toInt + distance)
        (times.toInt * distance)
        size
        [ok := ok], (ring: x.toInt + distance + times.toInt * distance = x.toInt + (Succ times).toInt * distance)
