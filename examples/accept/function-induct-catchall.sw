-- `countBelow.induct`: the `match` on `Ord.compare x k` has a catch-all
-- alternative, whose case gets the fact that the earlier alternative didn't
-- match (`notLess`).
import Std (Eq, List, Nat, Option, Ord, Ordering)

def countBelow (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..rest] =>
    match Ord.compare x k with
      | Less => Succ (countBelow k rest)
      | _ => countBelow k rest

theorem countBelowLe ∀ (k: Nat) (xs: List Nat): countBelow k xs ≤ List.length xs :=
  countBelow.induct k
    (xs result => result ≤ List.length xs)
    omega
    (x rest less ih => omega)
    (x rest notLess ih => omega)
    xs
