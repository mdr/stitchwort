-- Pairs with reject/plus-zero-by-rfl.sw: the same statement, by induction.
theorem plusZero: (n: Nat) -> n + 0 = n
  | Zero   => rfl
  | Succ m => Eq.cong Succ (plusZero m)
