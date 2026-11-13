-- Pairs with reject/plus-zero-by-rfl.sw: the same statement, by induction.
import Std (Eq)

theorem plusZero ∀ (n: Nat): n + 0 = n := match n with
  | Zero => rfl
  | Succ m => Eq.cong Succ (plusZero m)
