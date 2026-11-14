-- expect-error: E-NOT-A-TYPE
-- A `Bool` is read as the proposition that it is `True` where a proposition
-- is expected, but not as a side of `=`, nor the `∧` that side is made of:
-- that would make `p = (a ∧ b)` an equation between propositions by
-- accident. The note says to write `= True` out.
def sides (a b: Bool) (p: Prop) (h: p = (a ∧ b)): Nat := 0
