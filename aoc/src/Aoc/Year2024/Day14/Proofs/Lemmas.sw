--| General lemmas the day's proofs use: wrapping one tile at a time is
--| `Int.modNat`, and iterating a wrapped step is wrapping the sum.

namespace Aoc.Year2024.Day14.Proofs
import Aoc.Common.Proofs (modNatSmall)
import Std (Bool, DecEq, Eq, Int, List, Nat, Option, Void)

--| One tile forward on a line of `size` tiles is adding 1 and wrapping.
theorem forwardWrap: (size: Nat) → (x: Nat) → x < size →
    (if x + 1 == size then 0 else x + 1) = Int.modNat (x.toInt + 1) size
  | Zero, x, inside => Void.exfalso (Bool.falseNotTrue inside)
  | Succ n, x, inside =>
    match e: x + 1 == Succ n with
      | True => rewrite (omega [DecEq.sound e]: x = n) in Eq.sym (Nat.modSelf (Succ n))
      | False => Eq.sym (Nat.modSmall (x + 1) (Succ n) omega)

theorem mulNeZero: (a: Nat) → (b: Nat) → a ≠ 0 → b ≠ 0 → a * b ≠ 0
  | Zero, b, aPositive, bPositive, zero => aPositive rfl
  | a, Zero, aPositive, bPositive, zero => bPositive rfl
  | Succ a, Succ b, aPositive, bPositive, zero => omega

--| One tile back is subtracting 1 and wrapping.
theorem backwardWrap: (size: Nat) → (x: Nat) → x < size →
    (if x == 0 then size - 1 else x - 1) = Int.modNat (x.toInt - 1) size
  | Zero, x, inside => Void.exfalso (Bool.falseNotTrue inside)
  | Succ n, Zero, inside => rfl
  | Succ n, Succ x, inside =>
    rewrite (omega: (Succ x).toInt - 1 = x.toInt) in Eq.sym (Nat.modSmall x (Succ n) omega)

--| A step that adds `distance` and wraps, taken `times` times, adds
--| `times * distance` and wraps.
theorem iterateWrap (size: Nat) (distance: Int) (step: Nat → Nat)
    (wraps: (x: Nat) → x < size → step x = Int.modNat (x.toInt + distance) size):
    (times: Nat) → (x: Nat) → x < size → times.iterate step x = Int.modNat (x.toInt + times.toInt * distance) size
  | Zero, x, inside =>
    rewrite (ring: x.toInt + Nat.toInt 0 * distance = x.toInt) in Eq.sym (modNatSmall size x inside)
  | Succ times, x, inside =>
    let ok: size ≠ 0 := omega
    let stepInside: step x < size := rewrite wraps x inside in Int.modNatLt (x.toInt + distance) size [ok := ok]
    rewrite iterateWrap size distance step wraps times (step x) stepInside, wraps x inside,
      Int.modNatModAdd (x.toInt + distance) (times.toInt * distance) size [ok := ok],
      (ring: x.toInt + distance + times.toInt * distance = x.toInt + (Succ times).toInt * distance)
