-- `arithmetic` on `Int`: `+`, `-`, negation, multiplication by a number, `≤`,
-- `<`, `=` and `≠`, `x / k` and `x % k` for a nonzero number `k`, and
-- `n.toInt` of a `Nat`, which is never negative. `Int` atoms may be negative.

import Std (Int, Nat)

theorem stacked ∀ (x y z: Int) (h1: x ≤ y) (h2: y + 1 ≤ z): x < z := arithmetic

theorem subZero ∀ (a b: Int) (h: a - b = 0): a = b := arithmetic

theorem negation ∀ (x: Int): -(x + 3) + 2 * x = x - 3 := arithmetic

theorem timesRight ∀ (x: Int) (h: x * 3 < 7) (h2: 2 ≤ x): x = 2 := arithmetic

theorem negativeFactor ∀ (x: Int) (h: -2 * x ≤ 4): -2 ≤ x := arithmetic

-- No whole number is half of 1.
theorem notHalf ∀ (x: Int) (h: 2 * x = 1): Void := arithmetic

-- `Not`, `≠` and the comparisons' `False`.
theorem notLe ∀ (x y: Int) (h: ¬(x ≤ y)): y < x := arithmetic

theorem neLe ∀ (x y: Int) (h: x ≠ y) (h2: x ≤ y): x < y := arithmetic

theorem leqFalse ∀ (x y: Int) (h: x < y): Int.leq y x = False := arithmetic

theorem notEqual ∀ (x: Int) (h: 0 < x): x ≠ 0 := arithmetic

-- `Nat.toInt`: a `Nat` atom inside, with `0 ≤ n`.
theorem toIntNonneg ∀ (n: Nat) (x: Int) (h: x = n.toInt): 0 ≤ x := arithmetic

theorem predLess ∀ (n: Nat): n.toInt - 1 < n.toInt := arithmetic

theorem differenceNegative ∀ (m n: Nat) (h: m < n): m.toInt - n.toInt < 0 := arithmetic

theorem negatedNat ∀ (n: Nat) (x: Int) (h: x = -n.toInt) (h2: 0 < x): Void := arithmetic

-- Mixed: an `Int` fact about `Nat`s proves a `Nat` goal.
theorem backToNat ∀ (n: Nat) (h: n.toInt ≤ 3): n ≤ 3 := arithmetic

-- Division and remainder by a number: `k * (x / k) + x % k = x` and
-- `0 ≤ x % k < |k|`, rounding down for a positive `k`.
theorem divMul ∀ (k: Int): (3 * k) / 3 = k := arithmetic

theorem modMul ∀ (k: Int): (3 * k) % 3 = 0 := arithmetic

theorem modBounds ∀ (x: Int): 0 ≤ x % 5 ∧ x % 5 < 5 := arithmetic

theorem halfBounds ∀ (x: Int) (h: x / 2 = 3): 6 ≤ x ∧ x ≤ 7 := arithmetic

theorem negativeDivisor ∀ (x: Int): x % (-3) < 3 := arithmetic

theorem minusOneHalf: (-1) / 2 = -1 := arithmetic

-- By 0, `x / 0` and `x % 0` compute to `0` and `x`.
theorem divZero ∀ (x: Int): x / 0 = 0 := arithmetic

theorem modZero ∀ (x: Int): x % 0 = x := arithmetic

-- `x * y` and `y * x` are one unknown, by `Int.mulComm`.
theorem productOrder ∀ (x y: Int) (h: x * y = 5): y * x = 5 := arithmetic
