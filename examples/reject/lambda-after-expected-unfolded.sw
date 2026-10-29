-- expect-error: E-REWRITE-NOTHING
-- The two `_` of `List.sumByCong xs _ _ (x => …)` are taken from the
-- arguments of `List.sumBy` calls in the expected type. Written as the fold
-- `List.sumBy` computes to, the expected type has no such calls, and the
-- fold can't be compared while the `Add` dictionary is unknown, so the
-- callback's goal stays `?f1 xs x = ?f2 xs x`. Writing the two functions, or
-- the goal as `List.sumBy` calls, makes it check.
import Std (Eq, List, Nat)

theorem mulOneRight (n: Nat): n * 1 = n := omega

theorem unfolded (xs: List Nat):
    List.foldLeft xs 0 (acc x => acc + (x * 1)) = List.foldLeft xs 0 (acc x => acc + x) :=
  List.sumByCong xs _ _ (x => rewrite mulOneRight x in rfl)
