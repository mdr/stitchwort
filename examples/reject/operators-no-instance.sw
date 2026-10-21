-- expect-error: E-TYPE-MISMATCH
-- `+` on a type without an `Add` instance.
def both (x: Bool) (y: Bool): Bool := x + y
