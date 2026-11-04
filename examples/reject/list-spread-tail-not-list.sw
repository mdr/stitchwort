-- expect-error: E-TYPE-MISMATCH
-- What follows `..` is the rest of the list, not one more element.
def f (x: Nat): List Nat := [1, ..x]
