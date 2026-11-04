-- expect-error: E-PARSE
-- There is no `::`; the note points to `[x, ..xs]`.
def f (x: Nat) (xs: List Nat): List Nat := x :: xs
