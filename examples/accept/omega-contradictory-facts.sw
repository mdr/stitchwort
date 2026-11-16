-- When the arithmetic facts in scope contradict each other, `arithmetic` proves
-- the goal whatever it is, writing the refutation once and applying
-- `Void.impossible` to a proposition or `Void.absurd` to a type of data.
import Std (Nat, Bool, List)

-- A proposition whose sort isn't obvious from its head: `∈` is stuck on the
-- unknown list, so `arithmetic` asks the kernel what sort it has.
theorem membership ∀ (seat low: Nat) (rest: List Nat) (h1: seat + 1 = low) (h2: low ≤ seat - 1): seat + 1 ∈ rest :=
  arithmetic

-- A Bool equation that isn't a comparison against `True` or `False`.
theorem boolEquation ∀ (n: Nat) (h1: n < 2) (h2: n > 5): (n < 2) = (n > 5) := arithmetic

-- A type of data.
def aList (n: Nat) (h1: n < 2) (h2: n > 5): List Nat := arithmetic

-- And a function type, which `Void.absurd` also produces.
def aFunction (n: Nat) (h1: n < 2) (h2: n > 5): Nat → Nat := arithmetic
