-- expect-error: E-NOT-A-TYPE
-- `if h : …` needs a proposition, and `b` is a `Bool` value, not a proposition,
-- so `x < 3 && b` can't be the conjunction `And (x < 3) b`.
def f (b : Bool) (x : Nat) : Nat := if h : x < 3 && b then 1 else 0
