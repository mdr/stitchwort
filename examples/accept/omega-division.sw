-- `omega` and division or remainder by a number: `x / k` is an unknown `q`
-- with `q * k ≤ x < (q + 1) * k`, and `x % k` is `x - q * k`.

import Std (Nat)

theorem halfLe (n: Nat): n / 2 ≤ n := omega

theorem modLt (n: Nat): n % 3 < 3 := omega

theorem twiceHalfLe (n: Nat): 2 * (n / 2) ≤ n := omega

theorem halvesLe (n: Nat): n / 2 + n / 2 ≤ n := omega

theorem divModEq (n: Nat): (n / 4) * 4 + n % 4 = n := omega

-- Mixed with other facts.
theorem halfLess (n: Nat) (h: 2 ≤ n): n / 2 < n := omega

theorem thirdMono (m: Nat) (n: Nat) (h: m ≤ n): m / 3 ≤ n / 3 := omega

theorem halfOfBound (n: Nat) (k: Nat) (h: n < 2 * k): n / 2 < k := omega

theorem evenHalf (n: Nat) (h: n % 2 = 0): (n / 2) * 2 = n := omega

theorem smallDivZero (n: Nat) (h: n < 5): n / 5 = 0 := omega

-- Nested: a quarter is a half of a half.
theorem quarterLe (n: Nat): n / 2 / 2 ≤ n / 2 := omega
