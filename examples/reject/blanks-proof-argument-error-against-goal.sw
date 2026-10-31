-- expect-error: E-REFL
-- A proof argument after `_`s, inside `Eq.trans`, that fails against the
-- goal the expected type gives is blamed for that error (`True` and `False`
-- aren't equal), not for one against a goal of unknowns (`?6 0 rest h e (?7
-- 0 rest h e)` and `False`) (SW-931).
import Std (Bool, Decidable, Eq, List, Nat)

def zeros (xs: List Nat): List Nat := xs.filter (n => n == 0)

theorem skipThenRest (x: Nat) (rest: List Nat) (h: x = 0) (e: zeros rest = Nil): zeros (Cons x rest) = Nil :=
  Eq.trans (List.filterSkip _ _ _ (rewrite h in rfl)) e
