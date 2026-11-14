-- The `_`s of a lemma are known before its proof argument is checked, also
-- inside `Eq.trans`, where the middle of the equation is only fixed by the
-- second step: the call's type is compared with the goal first, and the
-- `rewrite` sees `(1 == 0) = False`, not a goal of unknowns (SW-931, from
-- AoC 2021 day 1's `windowsShort`).
import Std (Bool, Decidable, Eq, List, Nat)

def zeros (xs: List Nat): List Nat := xs.filter (n => n == 0)

theorem skipWhole ∀ (x: Nat) (rest: List Nat) (h: x = 1): zeros [x, ..rest] = zeros rest :=
  List.filterSkip _ _ _ (rewrite h in rfl)

theorem skipThenRest ∀ (x: Nat) (rest: List Nat) (h: x = 1) (e: zeros rest = []): zeros [x, ..rest] = [] :=
  Eq.trans (List.filterSkip _ _ _ (rewrite h in rfl)) e

theorem keepThenRest ∀ (x: Nat) (rest: List Nat) (h: x = 0) (e: zeros rest = []): zeros [x, ..rest] = [0] :=
  Eq.trans (List.filterKeep _ _ _ (rewrite h in rfl)) (rewrite h, e in rfl)
