-- expect-error: E-STD-NAMESPACE
-- The same, written from `Std`: refused on what the namespace is, not on how
-- it's spelt.
Std.List.sum : List Nat -> Nat
Std.List.sum xs = 0
