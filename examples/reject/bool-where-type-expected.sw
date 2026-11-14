-- expect-error: E-TYPE-MISMATCH
-- A `Bool` stands for a proposition only where a proposition is expected:
-- `List` wants a type of data, and `b` is not one.
def f (b: Bool) (xs: List b): Nat := 0
