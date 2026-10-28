-- In a statement `a != b` is the proposition `Not (a = b)`; ascribed, it is
-- the `Bool` that `!=` computes.
theorem notEqualBool: ((1 != 2): Bool) = True := rfl

theorem notEqualProp (same: Not (1 = 2)): 1 != 2 := same
