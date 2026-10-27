-- A congruence lemma whose call takes an `auto` dictionary, as
-- `List.sumByCong xs _ _ (x => …)` takes `Add b`: the lambda is checked again
-- after the call's type, `List.sumBy xs f1 = List.sumBy xs f2`, is compared
-- with the expected type. The dictionary is still unknown then, so what
-- `List.sumBy` computes to can't be compared; the two `_` are taken from the
-- arguments of the `List.sumBy` calls in the expected type instead.
import Std (Eq, List, Nat)

theorem addZeroRight (n: Nat): n + 0 = n := omega

theorem sumAddZero (xs: List Nat): List.sumBy xs (x => x + 0) = List.sumBy xs (x => x) :=
  List.sumByCong xs _ _ (x => rewrite addZeroRight x in rfl)

-- Through a definition that is a `List.sumBy` call, and with the callback's
-- goal mentioning a hypothesis.
def score (xs: List Nat) (ys: List Nat): Nat := xs.sumBy (x => x * ys.count (== x))

theorem scoreSameCounts (xs: List Nat) (ys: List Nat) (same: (p: Nat → Bool) → ys.count p = xs.count p):
    score xs ys = score xs xs :=
  List.sumByCong xs _ _ (x => rewrite same (== x) in rfl)

-- As a step of a `calc` chain.
theorem scoreTwice (xs: List Nat) (ys: List Nat) (same: (p: Nat → Bool) → ys.count p = xs.count p):
    score xs ys = score xs xs :=
  calc score xs ys
    _ = xs.sumBy (x => x * xs.count (== x)) := List.sumByCong xs _ _ (x => rewrite same (== x) in rfl)
    _ = score xs xs := rfl
