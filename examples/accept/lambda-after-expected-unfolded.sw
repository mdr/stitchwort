-- The two `_` of `List.sumByCong xs _ _ (x => …)` can't be read off the
-- expected type, which is written as the fold `List.sumBy` computes to and
-- has no `List.sumBy` calls. The fold's `Add` dictionary is the call's one
-- unknown instance, so the expected type picks it (SW-2864); then the fold
-- is compared and the callback's goal is `x * 1 = x`.
import Std (Eq, List, Nat)

theorem mulOneRight ∀ (n: Nat): n * 1 = n := omega

theorem unfolded ∀ (xs: List Nat):
    List.foldLeft xs 0 (acc x => acc + (x * 1)) = List.foldLeft xs 0 (acc x => acc + x) :=
  List.sumByCong xs _ _ (x => rewrite mulOneRight x in rfl)
