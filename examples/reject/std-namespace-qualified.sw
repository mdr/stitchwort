-- expect-error: E-STD-NAMESPACE
-- The same, written from `Std`: refused on what the namespace is, not on how
-- it's spelt.
def Std.List.sum (xs: List Nat): Nat := 0
