-- An unknown that the unfolding is stuck on is solved from the arguments of
-- the call around it: `lem _` against `pick True (two 4) = 2` solves `_`
-- with `True` from `pick`'s arguments, whose other argument, `two 3` against
-- `two 4`, is equal only by unfolding `two`. Comparing those arguments has
-- to unfold `two` there, as `pick ?b …` can't unfold to show it (SW-1506).
-- The unknown comes first in `pick` and last in `pickLast`.

def two (n: Nat): Nat := 2

def choose (b: Bool) (n: Nat): Nat := match b with
  | True => n
  | False => n

def pick (b: Bool) (n: Nat): Nat := choose b n

def pickLast (n: Nat) (b: Bool): Nat := choose b n

theorem lem ∀ (b: Bool): pick b (two 3) = 2 := match b with
  | True => rfl
  | False => rfl

theorem use: pick True (two 4) = 2 := lem _

theorem lemLast ∀ (b: Bool): pickLast (two 3) b = 2 := match b with
  | True => rfl
  | False => rfl

theorem useLast: pickLast (two 4) True = 2 := lemLast _
