-- A lemma about `≤` whose functions are left as `_`: the callback of
-- `List.sumByLe xs _ _ (x => …)` fails against `?g x ≤ ?f x`, so it is
-- checked again once the call's type, `List.sumBy xs g ≤ List.sumBy xs f`,
-- has been compared with the expected type, which fixes both.
import Std (Bool, Eq, List, Nat)

theorem keepMore (keep1: Nat → Bool) (keep2: Nat → Bool) (xs: List Nat)
    (included: (x: Nat) → keep1 x = True → keep2 x = True):
    List.sumBy xs (x => if keep1 x then x else 0) ≤ List.sumBy xs (x => if keep2 x then x else 0) :=
  List.sumByLe xs _ _ (x => match kept: keep1 x with
    | True => rewrite included x kept in Nat.leRefl x
    | False => Nat.zeroLe (if keep2 x then x else 0))

-- A proof that isn't a lambda's body but `omega`.
theorem plusOne (xs: List Nat): List.sumBy xs (x => x) ≤ List.sumBy xs (x => x + 1) :=
  List.sumByLe xs _ _ (x => omega)
