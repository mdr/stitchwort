-- What part 2 needs of `Nat.gcd`: it divides both numbers, and it is a
-- whole combination of them (Bézout's identity). Neither is in std.

namespace Aoc.Year2024.Day08.Proofs
import Std (And, Eq, Exists, Int, Nat)

-- One step of Euclid's algorithm.
theorem gcdStep (a: Nat) (c: Nat): Nat.gcd a (Succ c) = Nat.gcd (Succ c) (a % Succ c) := rewrite Nat.gcd.unfold a (Succ c) in rfl

theorem gcdZero (a: Nat): Nat.gcd a 0 = a := rewrite Nat.gcd.unfold a 0 in rfl

-- The gcd divides both numbers.
theorem gcdDivides (a: Nat) (b: Nat): And (∃ (x: Nat) => a = x * Nat.gcd a b) (∃ (y: Nat) => b = y * Nat.gcd a b)
    decreasing b
:=
  match b with
    | Zero => Both (Witness 1 (ring)) (Witness 0 rfl)
    | Succ c =>
      let divided := Nat.divModEq a (Succ c) (omega)
      match gcdDivides (Succ c) (a % Succ c) [decreasing := Nat.modLt a (Succ c)] with
        | Both (Witness x hx) (Witness y hy) =>
          rewrite gcdStep a c in
          Both (Witness (a / Succ c * x + y) (ring [divided, a / Succ c * hx, hy])) (Witness x hx)

-- Bézout's identity: the gcd is `s * a + t * b` for some integers `s` and
-- `t`.
theorem gcdBezout (a: Nat) (b: Nat): ∃ (s: Int) => ∃ (t: Int) => s * a.toInt + t * b.toInt = (Nat.gcd a b).toInt
    decreasing b
:=
  match b with
    | Zero => Witness 1 (Witness 0 (ring))
    | Succ c =>
      let divided := Eq.cong Nat.toInt (Nat.divModEq a (Succ c) (omega))
      match gcdBezout (Succ c) (a % Succ c) [decreasing := Nat.modLt a (Succ c)] with
        | Witness s (Witness t h) =>
          rewrite gcdStep a c in
          Witness t (Witness (s - t * (a / Succ c).toInt) (ring [h, t * divided]))
