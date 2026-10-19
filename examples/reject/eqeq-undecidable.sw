-- expect-error: E-AUTO-NONE
-- `==` needs a decision procedure for `=` on the type, and there's none for
-- functions.
def inc (x: Nat): Nat := x + 1

def same: Bool := inc == (\x => Succ x)
