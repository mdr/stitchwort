-- expect-error: E-UNSOLVED
-- `0 ≤ n` computes to `True = True` whatever `n` is, so in `Nat.zeroLe _`
-- against `0 ≤ (if keep2 x then x else 0)` nothing fixes the `_`: the goal
-- has already computed away what it was. Writing the argument makes it
-- check. Only this error is reported: the callback's first try, against
-- `?g x ≤ ?f x` before the call's type was compared with the goal, was
-- undone, and the other arm's error from it with it.
import Std (Bool, Eq, List, Nat)

theorem keepMore (keep1: Nat → Bool) (keep2: Nat → Bool) (xs: List Nat)
    (included: (x: Nat) → keep1 x = True → keep2 x = True):
    List.sumBy xs (x => if keep1 x then x else 0) ≤ List.sumBy xs (x => if keep2 x then x else 0) :=
  List.sumByLe xs _ _ (x => match kept: keep1 x with
    | True => rewrite included x kept in Nat.leRefl x
    | False => Nat.zeroLe _)
