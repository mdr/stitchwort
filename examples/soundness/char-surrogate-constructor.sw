-- expect-error: E-REFL
-- Building a surrogate with the constructor directly: `rfl` would have to
-- prove `Char.isScalar 55296 = True`, which computes to `False = True`.
def bad: Char := MkChar 55296 rfl
