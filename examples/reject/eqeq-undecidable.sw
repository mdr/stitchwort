-- expect-error: E-INSTANCE-NONE
-- `==` needs a `DecEq` instance for the type, and there's none for
-- functions.
def inc (x: Nat): Nat := x + 1

def same: Bool := inc == (x => Succ x)
