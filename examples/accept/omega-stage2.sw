-- `arithmetic`'s stage 2 (docs/proposals/omega.md, "As built (stage 2)"):
-- truncated subtraction, `Nat.max` and `Nat.min`, `a != b` facts, products
-- up to the order of their factors, and goals that aren't arithmetic when
-- the facts contradict each other. Each theorem below shows one case.

import Std (Nat, Bool, List)

-- Subtraction. What always holds (`a - b <= a`, `a <= (a - b) + b`) needs no
-- case split ...
theorem subLe ∀ (a b: Nat): a - b ≤ a := arithmetic

theorem leSubAdd ∀ (a b: Nat): a ≤ (a - b) + b := arithmetic

-- ... the rest splits on `b <= a` or `a < b` when it has to.
theorem subAddCancel ∀ (a b: Nat) (h: b ≤ a): (a - b) + b = a := arithmetic

theorem subZero ∀ (a b: Nat) (h: a < b): a - b = 0 := arithmetic

theorem subEqZeroLe ∀ (n m: Nat) (h: n - m = 0): n ≤ m := arithmetic

theorem predAddOne ∀ (x: Nat) (h: 0 < x): x - 1 + 1 = x := arithmetic

theorem subSub ∀ (a b c: Nat): a - b - c = a - (b + c) := arithmetic

theorem subSubSelf ∀ (n k: Nat) (h: k ≤ n): n - (n - k) = k := arithmetic

theorem subSuccRight ∀ (j t: Nat) (h: Succ j ≤ t): t - j = Succ (t - Succ j) := arithmetic

theorem subLtAdd ∀ (a b c: Nat) (h: a - b < c): a < b + c := arithmetic

-- `Nat.max` and `Nat.min`: their bounds always hold, and they split when needed.
theorem leMax ∀ (a b: Nat): a ≤ Nat.max a b := arithmetic

theorem maxLeAdd ∀ (a b: Nat): Nat.max a b ≤ a + b := arithmetic

theorem minLeMax ∀ (a b: Nat): Nat.min a b ≤ Nat.max a b := arithmetic

theorem minAddMax ∀ (a b: Nat): Nat.min a b + Nat.max a b = a + b := arithmetic

theorem maxOfLe ∀ (a b: Nat) (h: a ≤ b): Nat.max a b = b := arithmetic

-- `a != b` facts, written any of these ways, split into `a < b` or `b < a`.
theorem notEq ∀ (x y: Nat) (h: x ≠ y) (h2: x ≤ y): x < y := arithmetic

theorem neq ∀ (x y: Nat) (h: x ≠ y) (h2: x ≤ y): x < y := arithmetic

theorem equalFalse ∀ (x y: Nat) (e: Nat.equal x y = False) (h2: x ≤ y): x < y := arithmetic

theorem equalTrue ∀ (x y: Nat) (e: Nat.equal x y = True): x ≤ y := arithmetic

-- A product of two unknowns is an atom, the same whichever order its factors are in.
theorem mulComm ∀ (x y: Nat): x * y = y * x := arithmetic

theorem mulCommFact ∀ (k n t: Nat) (h: t + k * n ≤ 10) (h2: 3 ≤ n * k): t ≤ 7 := arithmetic

-- A goal that isn't arithmetic follows from facts that contradict each other:
-- a proposition, a `Bool` equation, or data.
theorem listGoal ∀ (xs: List Nat) (n: Nat) (h: n < 0): xs = [] := arithmetic

theorem boolGoal ∀ (b: Bool) (n: Nat) (h1: n < 3) (h2: 5 ≤ n): b = True := arithmetic

def dataGoal (n: Nat) (h: Succ n ≤ 0): List Nat := arithmetic
