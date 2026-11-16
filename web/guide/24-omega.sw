-- `arithmetic` proves facts about whole numbers and integers that use +, -,
-- comparisons, multiplication by constants and division by constants, using
-- the hypotheses in scope.
theorem triple ∀ (x: Nat): x * 3 = x + x + x := arithmetic

theorem between ∀ (a b: Nat) (h1: a < b) (h2: b ≤ 10): a < 10 := arithmetic

-- Subtraction stops at zero, and `arithmetic` knows it.
theorem monus ∀ (a b: Nat) (h: b ≤ a): a - b + b = a := arithmetic
