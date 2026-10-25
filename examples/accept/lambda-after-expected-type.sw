-- A lambda argument whose type still has unknowns is checked again after the
-- application's type has been compared with the expected type, if checking it
-- in place fails. Here `List.mapCong xs _ _ (x => …)`: its result type,
-- `List.map xs f1 = List.map xs f2`, depends on the arguments, so it can't be
-- compared before they're checked. In place, the callback's goal is
-- `?f1 x = ?f2 x`, where `rewrite` finds nothing; once the result is compared
-- with the theorem's statement, it's `x + 0 = x`.
import Std (Eq, List, Nat, Option)

theorem addZeroRight (n: Nat): n + 0 = n := omega

theorem mapAddZero (xs: List Nat): List.map xs (x => x + 0) = List.map xs (x => x) :=
  List.mapCong xs _ _ (x => rewrite addZeroRight x in rfl)

theorem filterMapAddZero (xs: List Nat): List.filterMap xs (x => Some (x + 0)) = List.filterMap xs (x => Some x) :=
  List.filterMapCong xs _ _ (x => rewrite addZeroRight x in rfl)

-- The same as a step of a `calc` chain, which says what each step proves.
theorem mapTwice (xs: List Nat): List.map xs (x => x + 0 + 0) = List.map xs (x => x) :=
  calc List.map xs (x => x + 0 + 0)
    _ = List.map xs (x => x + 0) := List.mapCong xs _ _ (x => rewrite addZeroRight (x + 0) in rfl)
    _ = List.map xs (x => x) := List.mapCong xs _ _ (x => rewrite addZeroRight x in rfl)
