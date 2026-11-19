-- expect-error: E-NO-INDUCT
-- A recursive call inside two local definitions that call each other isn't
-- followed: `m.induct` isn't made, and the error names the cycle instead of
-- walking it until the generator's budget runs out.
import Std (List, Nat)

def m (xs: List Nat): Nat := match xs with
  | [] => 0
  | [x, ..rest] =>
    def ev (k: Nat): Nat := match k with
      | Zero => m rest
      | Succ j => od j
    def od (k: Nat): Nat := match k with
      | Zero => 1
      | Succ j => ev j
    Succ (ev x)

theorem mAtLeastZero ∀ (xs: List Nat): m xs ≥ 0 := match induct (m xs) with
  | eq1 => arithmetic
  | eq2 x rest ih => arithmetic
