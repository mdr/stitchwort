-- expect-error: E-AUTO-NONE
-- `==` on a list needs `==` on its elements, and there's none for functions:
-- the error says which element type is missing one.
same : List (Nat -> Nat) -> Bool
same fs = fs == fs
