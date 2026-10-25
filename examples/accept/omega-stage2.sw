-- `omega`'s stage 2 (docs/proposals/omega.md, "As built (stage 2)"):
-- truncated subtraction, `Nat.max` and `Nat.min`, `a != b` facts, products
-- up to the order of their factors, and goals that aren't arithmetic when
-- the facts contradict each other. Each theorem below shows one case.

import Std (Nat, Bool, List)

-- Subtraction. What always holds (`a - b <= a`, `a <= (a - b) + b`) needs no
-- case split ...
theorem subLe (a: Nat) (b: Nat): a - b ≤ a := omega

theorem leSubAdd (a: Nat) (b: Nat): a ≤ (a - b) + b := omega

-- ... the rest splits on `b <= a` or `a < b` when it has to.
theorem subAddCancel (a: Nat) (b: Nat) (h: b ≤ a): (a - b) + b = a := omega

theorem subZero (a: Nat) (b: Nat) (h: a < b): a - b = 0 := omega

theorem subEqZeroLe (n: Nat) (m: Nat) (h: n - m = 0): n ≤ m := omega

theorem predAddOne (x: Nat) (h: 0 < x): x - 1 + 1 = x := omega

theorem subSub (a: Nat) (b: Nat) (c: Nat): a - b - c = a - (b + c) := omega

theorem subSubSelf (n: Nat) (k: Nat) (h: k ≤ n): n - (n - k) = k := omega

theorem subSuccRight (j: Nat) (t: Nat) (h: Succ j ≤ t): t - j = Succ (t - Succ j) := omega

theorem subLtAdd (a: Nat) (b: Nat) (c: Nat) (h: a - b < c): a < b + c := omega

-- `Nat.max` and `Nat.min`: their bounds always hold, and they split when needed.
theorem leMax (a: Nat) (b: Nat): a ≤ Nat.max a b := omega

theorem maxLeAdd (a: Nat) (b: Nat): Nat.max a b ≤ a + b := omega

theorem minLeMax (a: Nat) (b: Nat): Nat.min a b ≤ Nat.max a b := omega

theorem minAddMax (a: Nat) (b: Nat): Nat.min a b + Nat.max a b = a + b := omega

theorem maxOfLe (a: Nat) (b: Nat) (h: a ≤ b): Nat.max a b = b := omega

-- `a != b` facts, written any of these ways, split into `a < b` or `b < a`.
theorem notEq (x: Nat) (y: Nat) (h: Not (x = y)) (h2: x ≤ y): x < y := omega

theorem neq (x: Nat) (y: Nat) (h: x ≠ y) (h2: x ≤ y): x < y := omega

theorem equalFalse (x: Nat) (y: Nat) (e: Nat.equal x y = False) (h2: x ≤ y): x < y := omega

theorem equalTrue (x: Nat) (y: Nat) (e: Nat.equal x y = True): x ≤ y := omega

-- A product of two unknowns is an atom, the same whichever order its factors are in.
theorem mulComm (x: Nat) (y: Nat): x * y = y * x := omega

theorem mulCommFact (k: Nat) (n: Nat) (t: Nat) (h: t + k * n ≤ 10) (h2: 3 ≤ n * k): t ≤ 7 := omega

-- A goal that isn't arithmetic follows from facts that contradict each other:
-- a proposition, a `Bool` equation, or data.
theorem listGoal (xs: List Nat) (n: Nat) (h: n < 0): xs = Nil := omega

theorem boolGoal (b: Bool) (n: Nat) (h1: n < 3) (h2: 5 ≤ n): b = True := omega

def dataGoal (n: Nat) (h: Succ n ≤ 0): List Nat := omega
