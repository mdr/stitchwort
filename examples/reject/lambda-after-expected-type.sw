-- expect-error: E-REWRITE-NOTHING
-- A lambda argument that fails in place and again after the application's
-- type has been compared with the expected type is blamed against the goal
-- as that comparison left it: `x + 1 = x`, not `?f1 xs x = ?f2 xs x`.
-- (`x => rfl` would not show this: in place it succeeds by making the two
-- functions the same, and then the whole call is the wrong type.)
import Std (Eq, List, Nat)

theorem addZeroRight (n: Nat): n + 0 = n := omega

theorem wrongCong (xs: List Nat): List.map xs (x => x + 1) = List.map xs (x => x) :=
  List.mapCong xs _ _ (x => rewrite addZeroRight x in rfl)
