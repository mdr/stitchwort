-- `ring [c * h]`: a hypothesis `h: l = r` times a coefficient, any `Nat` or
-- `Int` expression. The goal's left minus its right must be the sum of each
-- coefficient times its hypothesis's `l - r`.

import Std (Nat, Int)

theorem scaled (a: Int) (b: Int) (h: a = 2 * b): 4 * a = 8 * b := ring [4 * h]

-- A variable coefficient, and two of them.
theorem byVariable (x: Int) (a: Int) (b: Int) (h: a = b): x * a + 1 = x * b + 1 := ring [x * h]

theorem bothScaled (x: Int) (y: Int) (k: Int) (sum: x + y = 10) (gap: x - y = 2): 2 * k * x = 12 * k := ring [k * sum, k * gap]

-- `-h` turns `h` round; a negative literal coefficient does too.
theorem negated (a: Int) (b: Int) (h: a = b + 1): b - a = -1 := ring [-h]

theorem negativeLiteral (a: Int) (b: Int) (c: Int) (h: a = b): c - 4 * a = c - 4 * b := ring [-4 * h]

-- One entry can be a combination: `3 * h1 + h2` is two hypotheses.
theorem combination (a: Int) (b: Int) (c: Int) (h1: a = b) (h2: b = c): 3 * a - c = 2 * b := ring [3 * h1 + h2]

-- Coefficients multiply: `2 * (x * h)` is `2 * x` times `h`.
theorem nested (a: Int) (b: Int) (x: Int) (h: a = b): 2 * x * a = 2 * x * b := ring [2 * (x * h)]

-- At `Nat` there is no subtraction: `-h` means the hypothesis turned round.
theorem natScaled (a: Nat) (b: Nat) (h: a = b + 1): 3 * a = 3 * b + 3 := ring [3 * h]

theorem natNegated (a: Nat) (b: Nat) (h: a + 1 = b): b = a + 1 := ring [-h]

-- Without a `-`, a hypothesis is tried either way round, coefficient or not.
theorem natEitherWay (a: Nat) (b: Nat) (n: Nat) (h: a = b + 1): n * b + n = n * a := ring [n * h]

-- Lagrange's identity in two dimensions, from AoC 2024 day 8: with
-- `u × v = 0` and `|u|² = 4|v|²`, `(u · v)² = (2|v|²)²`.
theorem lagrange (ur: Int) (uc: Int) (vr: Int) (vc: Int) (cross: ur * vc - uc * vr = 0)
    (distance: ur * ur + uc * uc = 4 * (vr * vr + vc * vc)):
    (ur * vr + uc * vc) * (ur * vr + uc * vc) = (2 * (vr * vr + vc * vc)) * (2 * (vr * vr + vc * vc)) :=
  ring [(vr * vr + vc * vc) * distance, -(ur * vc - uc * vr) * cross]
