-- Pairs with reject/plus-zero-by-rfl.sw: the same statement, by induction.
theorem plusZero : (n : Nat) -> n + 0 = n
plusZero Zero     = rfl
plusZero (Succ m) = Eq.cong Succ (plusZero m)
