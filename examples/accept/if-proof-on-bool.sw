-- `if h: b` on a `Bool` is on the proposition `b = True`, so `h: b` in the
-- `then` branch.
def pick (b: Bool): Nat := if h: b then 1 else 2
