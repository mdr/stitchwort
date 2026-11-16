-- `arithmetic` and `Int.natAbs`: for each `Int.natAbs t` among the atoms it
-- splits on `Int.natAbsDichotomy t`, `(0 ≤ t ∧ |t| = t) ∨ (t < 0 ∧ |t| = -t)`,
-- when the goal doesn't follow without it.

import Std (Nat, Int)

theorem leAbs ∀ (x: Int): x ≤ Nat.toInt x.natAbs := arithmetic

theorem negLeAbs ∀ (x: Int): 0 - x ≤ Nat.toInt x.natAbs := arithmetic

theorem absNegate ∀ (x: Int): (0 - x).natAbs = x.natAbs := arithmetic

theorem absSubComm ∀ (x y: Int): (x - y).natAbs = (y - x).natAbs := arithmetic

theorem absAdd ∀ (x y: Int): (x + y).natAbs ≤ x.natAbs + y.natAbs := arithmetic

theorem triangle ∀ (a b c: Int): (a - c).natAbs ≤ (a - b).natAbs + (b - c).natAbs := arithmetic

theorem reverseTriangle ∀ (x y: Int): x.natAbs - y.natAbs ≤ (x - y).natAbs := arithmetic

-- From a fact about a size.
theorem belowOfAbs ∀ (x: Int) (h: x.natAbs ≤ 3): x ≤ 3 := arithmetic

theorem aboveOfAbs ∀ (x: Int) (h: x.natAbs ≤ 3): 0 - 3 ≤ x := arithmetic

theorem zeroOfAbs ∀ (x: Int) (h: x.natAbs = 0): x = 0 := arithmetic

-- Inside a size: `||x| - 1|` is at most `|x|`, for `x ≠ 0`.
theorem nested ∀ (x: Int) (h: x ≠ 0): (Nat.toInt x.natAbs - 1).natAbs ≤ x.natAbs := arithmetic
