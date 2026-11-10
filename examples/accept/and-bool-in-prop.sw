-- A `Bool` operand of `∧` where a proposition is expected is that `Bool`
-- being `True`: `if h: x < 3 ∧ b` is on `x < 3 ∧ b = True`.
def f (b: Bool) (x: Nat): Nat := if h: x < 3 ∧ b then 1 else 0
