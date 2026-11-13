-- In a statement `a != b` is the proposition `Not (a = b)`; ascribed, it is
-- the `Bool` that `!=` computes.
theorem notEqualBool: ((1 != 2): Bool) = True := rfl

theorem notEqualProp ∀ (same: 1 ≠ 2): 1 != 2 := same

-- The ascription parses in a binder's type, after `→` or in a lambda's
-- parameter.
theorem nonEmptyBool ∀ (xs: List Nat) (nonEmpty: ((xs != []): Bool) = True): (xs == []) = False := match xs with
  | [x, ..rest] => rfl

def firstOr (fallback: Nat): Nat :=
  let first := (xs: List Nat) (nonEmpty: ((xs != []): Bool) = True) => xs.getOr 0 fallback
  first [fallback] rfl
