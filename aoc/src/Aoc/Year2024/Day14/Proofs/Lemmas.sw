-- General lemmas the day's proofs use: wrapping one tile at a time is
-- `Int.modNat`, and iterating a wrapped step is wrapping the sum.

namespace Aoc.Year2024.Day14.Proofs
import Std (Bool, DecEq, Eq, Int, List, Nat, Option, Void)

-- One tile forward on a line of `size` tiles is adding 1 and wrapping.
theorem forwardWrap: (size: Nat) → (ok: size ≠ 0) → (x: Nat) → x < size →
    (if x + 1 == size then 0 else x + 1) = Int.modNat (x.toInt + 1) size [ok := ok]
  | Zero, ok, x, inside => Void.exfalso (ok rfl)
  | Succ n, ok, x, inside =>
    match e: x + 1 == Succ n with
      | True => rewrite DecEq.sound (x + 1) (Succ n) e in Eq.sym (Nat.modSelf (Succ n))
      | False => Eq.sym (Nat.modSmall (x + 1) (Succ n) omega)

-- Counting `wanted` among the `Some` results is counting the elements that
-- give `Some wanted`.
theorem countFilterMap [auto eq: DecEq b] (f: a → Option b) (wanted: b):
    (xs: List a) → (xs.filterMap f).count (== wanted) = xs.count (x => f x == Some wanted)
  | Nil => rfl
  | Cons x rest =>
    rewrite List.countCons rest x (y => f y == Some wanted)
    in match e: f x with
      | None => countFilterMap f wanted rest
      | Some found =>
        rewrite List.countCons (rest.filterMap f) found (== wanted), Option.someBeqSome found wanted
        in Eq.cong (count => Bool.toNat (found == wanted) + count) (countFilterMap f wanted rest)

theorem mulNeZero: (a: Nat) → (b: Nat) → a ≠ 0 → b ≠ 0 → a * b ≠ 0
  | Zero, b, aPositive, bPositive, zero => aPositive rfl
  | a, Zero, aPositive, bPositive, zero => bPositive rfl
  | Succ a, Succ b, aPositive, bPositive, zero => omega

-- One tile back is subtracting 1 and wrapping.
theorem backwardWrap: (size: Nat) → (ok: size ≠ 0) → (x: Nat) → x < size →
    (if x == 0 then size - 1 else x - 1) = Int.modNat (x.toInt - 1) size [ok := ok]
  | Zero, ok, x, inside => Void.exfalso (ok rfl)
  | Succ n, ok, Zero, inside => rfl
  | Succ n, ok, Succ x, inside =>
    rewrite toIntPred (Succ x) omega in Eq.sym (Nat.modSmall x (Succ n) omega)

-- Stated over a variable so that `omega` sees `y.toInt - 1`, not what
-- `Succ x` computes to.
theorem toIntPred (y: Nat) (positive: 0 < y): y.toInt - 1 = (y - 1).toInt := omega

-- A tile inside the space wraps to itself.
theorem modNatSmall: (size: Nat) → (ok: size ≠ 0) → (x: Nat) → x < size → Int.modNat x.toInt size [ok := ok] = x
  | Zero, ok, x, inside => Void.exfalso (ok rfl)
  | Succ n, ok, x, inside => Nat.modSmall x (Succ n) inside

-- A step that adds `distance` and wraps, taken `times` times, adds
-- `times * distance` and wraps.
theorem iterateWrap (size: Nat) (ok: size ≠ 0) (distance: Int) (step: Nat → Nat)
    (wraps: (x: Nat) → x < size → step x = Int.modNat (x.toInt + distance) size [ok := ok]):
    (times: Nat) → (x: Nat) → x < size → times.iterate step x = Int.modNat (x.toInt + times.toInt * distance) size [ok := ok]
  | Zero, x, inside =>
    rewrite (ring: x.toInt + Nat.toInt 0 * distance = x.toInt) in Eq.sym (modNatSmall size ok x inside)
  | Succ times, x, inside =>
    let stepInside: step x < size := rewrite wraps x inside in Int.modNatLt (x.toInt + distance) size [ok := ok]
    rewrite iterateWrap size ok distance step wraps times (step x) stepInside, wraps x inside,
      Int.modNatModAdd (x.toInt + distance) (times.toInt * distance) size [ok := ok],
      (ring: x.toInt + distance + times.toInt * distance = x.toInt + (Succ times).toInt * distance)
