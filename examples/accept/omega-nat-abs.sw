-- `omega` and `Int.natAbs`: for each `Int.natAbs t` among the atoms it
-- splits on `Int.natAbsDichotomy t`, `(0 ≤ t ∧ |t| = t) ∨ (t < 0 ∧ |t| = -t)`,
-- when the goal doesn't follow without it.

import Std (Nat, Int)

theorem leAbs ∀ (x: Int): x ≤ Nat.toInt x.natAbs := omega

theorem negLeAbs ∀ (x: Int): 0 - x ≤ Nat.toInt x.natAbs := omega

theorem absNegate ∀ (x: Int): (0 - x).natAbs = x.natAbs := omega

theorem absSubComm ∀ (x: Int) (y: Int): (x - y).natAbs = (y - x).natAbs := omega

theorem absAdd ∀ (x: Int) (y: Int): (x + y).natAbs ≤ x.natAbs + y.natAbs := omega

theorem triangle ∀ (a: Int) (b: Int) (c: Int): (a - c).natAbs ≤ (a - b).natAbs + (b - c).natAbs := omega

theorem reverseTriangle ∀ (x: Int) (y: Int): x.natAbs - y.natAbs ≤ (x - y).natAbs := omega

-- From a fact about a size.
theorem belowOfAbs ∀ (x: Int) (h: x.natAbs ≤ 3): x ≤ 3 := omega

theorem aboveOfAbs ∀ (x: Int) (h: x.natAbs ≤ 3): 0 - 3 ≤ x := omega

theorem zeroOfAbs ∀ (x: Int) (h: x.natAbs = 0): x = 0 := omega

-- Inside a size: `||x| - 1|` is at most `|x|`, for `x ≠ 0`.
theorem nested ∀ (x: Int) (h: x ≠ 0): (Nat.toInt x.natAbs - 1).natAbs ≤ x.natAbs := omega
