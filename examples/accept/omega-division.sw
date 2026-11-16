-- `arithmetic` and division or remainder by a number: `x / k` is an unknown `q`
-- with `q * k ≤ x < (q + 1) * k`, and `x % k` is `x - q * k`.

import Std (Nat)

theorem halfLe ∀ (n: Nat): n / 2 ≤ n := arithmetic

theorem modLt ∀ (n: Nat): n % 3 < 3 := arithmetic

theorem twiceHalfLe ∀ (n: Nat): 2 * (n / 2) ≤ n := arithmetic

theorem halvesLe ∀ (n: Nat): n / 2 + n / 2 ≤ n := arithmetic

theorem divModEq ∀ (n: Nat): (n / 4) * 4 + n % 4 = n := arithmetic

-- Mixed with other facts.
theorem halfLess ∀ (n: Nat) (h: 2 ≤ n): n / 2 < n := arithmetic

theorem thirdMono ∀ (m n: Nat) (h: m ≤ n): m / 3 ≤ n / 3 := arithmetic

theorem halfOfBound ∀ (n k: Nat) (h: n < 2 * k): n / 2 < k := arithmetic

theorem evenHalf ∀ (n: Nat) (h: n % 2 = 0): (n / 2) * 2 = n := arithmetic

theorem smallDivZero ∀ (n: Nat) (h: n < 5): n / 5 = 0 := arithmetic

-- Nested: a quarter is a half of a half.
theorem quarterLe ∀ (n: Nat): n / 2 / 2 ≤ n / 2 := arithmetic

-- By 0: `n / 0 = 0` (`Nat.divFuelZero`, whatever the fuel), so `n % 0 = n`.
theorem divZero ∀ (n: Nat): n / 0 = 0 := arithmetic

theorem succDivZero ∀ (n: Nat): (n + 1) / 0 = 0 := arithmetic

theorem modZero ∀ (n: Nat): n % 0 = n := arithmetic

theorem divZeroLe ∀ (m n: Nat): m / 0 ≤ n := arithmetic
