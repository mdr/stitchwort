-- `omega` on `Int`: `+`, `-`, negation, multiplication by a number, `≤`,
-- `<`, `=` and `≠`, `x / k` and `x % k` for a nonzero number `k`, and
-- `n.toInt` of a `Nat`, which is never negative. `Int` atoms may be negative.

import Std (Int, Nat)

theorem stacked (x: Int) (y: Int) (z: Int) (h1: x ≤ y) (h2: y + 1 ≤ z): x < z := omega

theorem subZero (a: Int) (b: Int) (h: a - b = 0): a = b := omega

theorem negation (x: Int): -(x + 3) + 2 * x = x - 3 := omega

theorem timesRight (x: Int) (h: x * 3 < 7) (h2: 2 ≤ x): x = 2 := omega

theorem negativeFactor (x: Int) (h: -2 * x ≤ 4): -2 ≤ x := omega

-- No whole number is half of 1.
theorem notHalf (x: Int) (h: 2 * x = 1): Void := omega

-- `Not`, `≠` and the comparisons' `False`.
theorem notLe (x: Int) (y: Int) (h: Not (x ≤ y)): y < x := omega

theorem neLe (x: Int) (y: Int) (h: x ≠ y) (h2: x ≤ y): x < y := omega

theorem leqFalse (x: Int) (y: Int) (h: x < y): Int.leq y x = False := omega

theorem notEqual (x: Int) (h: 0 < x): x ≠ 0 := omega

-- `Nat.toInt`: a `Nat` atom inside, with `0 ≤ n`.
theorem toIntNonneg (n: Nat) (x: Int) (h: x = n.toInt): 0 ≤ x := omega

theorem predLess (n: Nat): n.toInt - 1 < n.toInt := omega

theorem differenceNegative (m: Nat) (n: Nat) (h: m < n): m.toInt - n.toInt < 0 := omega

theorem negatedNat (n: Nat) (x: Int) (h: x = -n.toInt) (h2: 0 < x): Void := omega

-- Mixed: an `Int` fact about `Nat`s proves a `Nat` goal.
theorem backToNat (n: Nat) (h: n.toInt ≤ 3): n ≤ 3 := omega

-- Division and remainder by a number: `k * (x / k) + x % k = x` and
-- `0 ≤ x % k < |k|`, rounding down for a positive `k`.
theorem divMul (k: Int): (3 * k) / 3 = k := omega

theorem modMul (k: Int): (3 * k) % 3 = 0 := omega

theorem modBounds (x: Int): 0 ≤ x % 5 ∧ x % 5 < 5 := omega

theorem halfBounds (x: Int) (h: x / 2 = 3): 6 ≤ x ∧ x ≤ 7 := omega

theorem negativeDivisor (x: Int): x % (-3) < 3 := omega

theorem minusOneHalf: (-1) / 2 = -1 := omega

-- `x * y` and `y * x` are one unknown, by `Int.mulComm`.
theorem productOrder (x: Int) (y: Int) (h: x * y = 5): y * x = 5 := omega
