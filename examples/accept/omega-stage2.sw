-- `omega`'s stage 2 (docs/proposals/omega.md, "As built (stage 2)"):
-- truncated subtraction, `Nat.max` and `Nat.min`, `a != b` facts, products
-- up to the order of their factors, and goals that aren't arithmetic when
-- the facts contradict each other. Each theorem below shows one case.

import Std (Nat, Bool, List)

-- Subtraction. What always holds (`a - b <= a`, `a <= (a - b) + b`) needs no
-- case split ...
theorem subLe ∀ (a b: Nat): a - b ≤ a := omega

theorem leSubAdd ∀ (a b: Nat): a ≤ (a - b) + b := omega

-- ... the rest splits on `b <= a` or `a < b` when it has to.
theorem subAddCancel ∀ (a b: Nat) (h: b ≤ a): (a - b) + b = a := omega

theorem subZero ∀ (a b: Nat) (h: a < b): a - b = 0 := omega

theorem subEqZeroLe ∀ (n m: Nat) (h: n - m = 0): n ≤ m := omega

theorem predAddOne ∀ (x: Nat) (h: 0 < x): x - 1 + 1 = x := omega

theorem subSub ∀ (a b c: Nat): a - b - c = a - (b + c) := omega

theorem subSubSelf ∀ (n k: Nat) (h: k ≤ n): n - (n - k) = k := omega

theorem subSuccRight ∀ (j t: Nat) (h: Succ j ≤ t): t - j = Succ (t - Succ j) := omega

theorem subLtAdd ∀ (a b c: Nat) (h: a - b < c): a < b + c := omega

-- `Nat.max` and `Nat.min`: their bounds always hold, and they split when needed.
theorem leMax ∀ (a b: Nat): a ≤ Nat.max a b := omega

theorem maxLeAdd ∀ (a b: Nat): Nat.max a b ≤ a + b := omega

theorem minLeMax ∀ (a b: Nat): Nat.min a b ≤ Nat.max a b := omega

theorem minAddMax ∀ (a b: Nat): Nat.min a b + Nat.max a b = a + b := omega

theorem maxOfLe ∀ (a b: Nat) (h: a ≤ b): Nat.max a b = b := omega

-- `a != b` facts, written any of these ways, split into `a < b` or `b < a`.
theorem notEq ∀ (x y: Nat) (h: x ≠ y) (h2: x ≤ y): x < y := omega

theorem neq ∀ (x y: Nat) (h: x ≠ y) (h2: x ≤ y): x < y := omega

theorem equalFalse ∀ (x y: Nat) (e: Nat.equal x y = False) (h2: x ≤ y): x < y := omega

theorem equalTrue ∀ (x y: Nat) (e: Nat.equal x y = True): x ≤ y := omega

-- A product of two unknowns is an atom, the same whichever order its factors are in.
theorem mulComm ∀ (x y: Nat): x * y = y * x := omega

theorem mulCommFact ∀ (k n t: Nat) (h: t + k * n ≤ 10) (h2: 3 ≤ n * k): t ≤ 7 := omega

-- A goal that isn't arithmetic follows from facts that contradict each other:
-- a proposition, a `Bool` equation, or data.
theorem listGoal ∀ (xs: List Nat) (n: Nat) (h: n < 0): xs = [] := omega

theorem boolGoal ∀ (b: Bool) (n: Nat) (h1: n < 3) (h2: 5 ≤ n): b = True := omega

def dataGoal (n: Nat) (h: Succ n ≤ 0): List Nat := omega
