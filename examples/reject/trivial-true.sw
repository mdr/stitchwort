-- expect-error: E-NO-READING
-- `True` as a proposition is the test fact `True = True`, which `rfl`
-- proves; `Trivial` is the proof of `Unit`, so the error should say to use
-- `rfl` (SW-3455).

theorem t: True := Trivial
