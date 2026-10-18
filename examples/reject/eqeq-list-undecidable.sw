-- expect-error: E-AUTO-NONE
-- `==` on a list needs `==` on its elements, and there's none for functions:
-- the error says which element type is missing one.
def same (fs : List (Nat -> Nat)) : Bool := fs == fs
