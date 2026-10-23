-- expect-error: E-REFL
-- An error in one branch doesn't hide a hole in another: branches are
-- checked independently.
theorem addZero (n: Nat): n + 0 = n :=
  match n with
    | Zero => ?
    | Succ k => rfl
