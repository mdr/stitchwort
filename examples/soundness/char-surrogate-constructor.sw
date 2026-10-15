-- expect-error: E-REFL
-- Building a surrogate with the constructor directly: `rfl` would have to
-- prove `isScalar 55296 = True`, which computes to `False = True`.
bad : Char
bad = MkChar 55296 rfl
