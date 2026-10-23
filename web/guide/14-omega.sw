-- `omega` proves facts about whole numbers that only use +, comparisons and
-- multiplication by constants, using the hypotheses in scope.
theorem triple (x: Nat): x * 3 = x + x + x := omega

theorem between (a: Nat) (b: Nat) (h1: a < b) (h2: b <= 10): a < 10 := omega

-- Subtraction stops at zero, and `omega` knows it.
theorem monus (a: Nat) (b: Nat) (h: b <= a): a - b + b = a := omega
