-- expect-error: E-REFL
-- An error in one branch doesn't hide a hole in another: branches are
-- checked independently.
theorem zeroMul (n: Nat): 0 * n = n * 0 :=
  match n with
    | Zero => ?
    | Succ k => rfl
