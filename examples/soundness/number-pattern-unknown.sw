-- expect-error: E-REFL
-- For an unknown `x`, `hit x` can't be computed: `x` might be 404. Failing
-- to show that `x` is 404 doesn't mean it isn't.
hit : Nat -> Bool
hit 404 = True
hit _   = False

theorem bad : (x : Nat) -> hit x = False
bad x = rfl
