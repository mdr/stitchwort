-- `ring` proves equations that hold by the laws of + and * (commutative
-- semiring laws over Nat, ring laws over Int): it puts both sides in a normal
-- form, a sum of monomials, and writes a proof by the Std.Ring soundness
-- theorem. Anything it does not understand (a call, `a - b` on Nat, `x / y`)
-- is an opaque atom.

import Std (Nat, Int, List)

theorem comm (x: Nat) (y: Nat): x + y = y + x := ring

theorem distrib (a: Nat) (b: Nat) (c: Nat): a * (b + c) = a * b + a * c := ring

theorem square (x: Nat): (x + 1) * (x + 1) = x * x + 2 * x + 1 := ring

-- `Succ` is `+ 1`, numerals are constants, and `Nat.pow` with a literal exponent multiplies out.
theorem succs (x: Nat) (y: Nat): Succ x * Succ y = x * y + x + y + 1 := ring

theorem pow2 (x: Nat): Nat.pow x 2 = x * x := ring

theorem literals: 2 * 3 + 4 = 10 := ring

-- Degree four.
theorem fourth (a: Nat) (b: Nat): (a + b) * (a + b) * (a + b) * (a + b) = Nat.pow a 4 + 4 * Nat.pow a 3 * b + 6 * a * a * b * b + 4 * a * Nat.pow b 3 + Nat.pow b 4 := ring

-- Over Int, negation and subtraction cancel.
theorem difference (a: Int) (b: Int): (a + b) * (a - b) = a * a - b * b := ring

theorem negNeg (a: Int): -(-a) = a := ring

theorem subCancel (d: Int): d + (1 - d) = 1 := ring

-- `toInt` of a Nat sum is the Int sum.
theorem toIntAdd (x: Nat) (y: Nat): x.toInt + y.toInt = (y + x).toInt := ring

-- Calls are atoms: `List.length xs` is one unknown.
theorem lengthAtom (xs: List Nat) (b: Nat): b * List.length xs + b = b * (List.length xs + 1) := ring

-- `ring [h]` also uses equations: the goal holds once each is added, scaled as needed.
theorem pairsStep (n: Nat) (p: Nat) (h: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n := ring [h]

-- A hypothesis is used whichever way round the goal needs it: here `c` is replaced by `a + b`.
theorem eitherWay (a: Nat) (b: Nat) (c: Nat) (h: a + b = c): c + c = a + b + c := ring [h]

-- `(ring: a = b)` states the equation, here as a rewrite rule.
theorem asRule (x: Nat) (y: Nat) (f: Nat → Nat): f (x * y) = f (y * x) := rewrite (ring: x * y = y * x)

-- And as a calc step.
theorem viaCalc (x: Nat): x + x = 2 * x :=
  calc x + x
    _ = 2 * x := ring
