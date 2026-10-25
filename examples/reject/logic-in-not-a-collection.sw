-- expect-error: E-TYPE-MISMATCH
-- `in` needs a list, a set or a map on its right (D1201); the error names the
-- type it got.
def inNumber (x: Nat) (n: Nat): Bool := x in n
